%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:41 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.69s
% Verified   : 
% Statistics : Number of formulae       :  379 (21983 expanded)
%              Number of leaves         :   51 (7436 expanded)
%              Depth                    :   38
%              Number of atoms          : 2048 (170629 expanded)
%              Number of equality atoms :   92 (5103 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_12 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

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

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k6_yellow_6,type,(
    k6_yellow_6: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_318,negated_conjecture,(
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

tff(f_265,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(f_212,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(f_188,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

tff(f_165,axiom,(
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

tff(f_241,axiom,(
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

tff(c_94,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_104,plain,
    ( ~ v2_struct_0('#skF_11')
    | ~ v1_compts_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_132,plain,(
    ~ v1_compts_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_92,plain,(
    v2_pre_topc('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_90,plain,(
    l1_pre_topc('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_66,plain,(
    ! [A_160] :
      ( v4_orders_2('#skF_7'(A_160))
      | v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_64,plain,(
    ! [A_160] :
      ( v7_waybel_0('#skF_7'(A_160))
      | v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_62,plain,(
    ! [A_160] :
      ( l1_waybel_0('#skF_7'(A_160),A_160)
      | v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

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

tff(c_364,plain,(
    ! [A_314,B_315,D_316] :
      ( m1_connsp_2('#skF_1'(A_314,B_315,k10_yellow_6(A_314,B_315),D_316),A_314,D_316)
      | r2_hidden(D_316,k10_yellow_6(A_314,B_315))
      | ~ m1_subset_1(D_316,u1_struct_0(A_314))
      | ~ m1_subset_1(k10_yellow_6(A_314,B_315),k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_waybel_0(B_315,A_314)
      | ~ v7_waybel_0(B_315)
      | ~ v4_orders_2(B_315)
      | v2_struct_0(B_315)
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_367,plain,(
    ! [A_93,B_94,D_316] :
      ( m1_connsp_2('#skF_1'(A_93,B_94,k10_yellow_6(A_93,B_94),D_316),A_93,D_316)
      | r2_hidden(D_316,k10_yellow_6(A_93,B_94))
      | ~ m1_subset_1(D_316,u1_struct_0(A_93))
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_32,c_364])).

tff(c_375,plain,(
    ! [A_320,B_321,C_322,E_323] :
      ( r2_hidden('#skF_2'(A_320,B_321,C_322),C_322)
      | r1_waybel_0(A_320,B_321,E_323)
      | ~ m1_connsp_2(E_323,A_320,'#skF_2'(A_320,B_321,C_322))
      | k10_yellow_6(A_320,B_321) = C_322
      | ~ m1_subset_1(C_322,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_waybel_0(B_321,A_320)
      | ~ v7_waybel_0(B_321)
      | ~ v4_orders_2(B_321)
      | v2_struct_0(B_321)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | v2_struct_0(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_593,plain,(
    ! [A_457,B_458,C_459,B_460] :
      ( r2_hidden('#skF_2'(A_457,B_458,C_459),C_459)
      | r1_waybel_0(A_457,B_458,'#skF_1'(A_457,B_460,k10_yellow_6(A_457,B_460),'#skF_2'(A_457,B_458,C_459)))
      | k10_yellow_6(A_457,B_458) = C_459
      | ~ m1_subset_1(C_459,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_waybel_0(B_458,A_457)
      | ~ v7_waybel_0(B_458)
      | ~ v4_orders_2(B_458)
      | v2_struct_0(B_458)
      | r2_hidden('#skF_2'(A_457,B_458,C_459),k10_yellow_6(A_457,B_460))
      | ~ m1_subset_1('#skF_2'(A_457,B_458,C_459),u1_struct_0(A_457))
      | ~ l1_waybel_0(B_460,A_457)
      | ~ v7_waybel_0(B_460)
      | ~ v4_orders_2(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_367,c_375])).

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

tff(c_613,plain,(
    ! [A_461,B_462,C_463] :
      ( ~ m1_subset_1(k10_yellow_6(A_461,B_462),k1_zfmisc_1(u1_struct_0(A_461)))
      | r2_hidden('#skF_2'(A_461,B_462,C_463),C_463)
      | k10_yellow_6(A_461,B_462) = C_463
      | ~ m1_subset_1(C_463,k1_zfmisc_1(u1_struct_0(A_461)))
      | r2_hidden('#skF_2'(A_461,B_462,C_463),k10_yellow_6(A_461,B_462))
      | ~ m1_subset_1('#skF_2'(A_461,B_462,C_463),u1_struct_0(A_461))
      | ~ l1_waybel_0(B_462,A_461)
      | ~ v7_waybel_0(B_462)
      | ~ v4_orders_2(B_462)
      | v2_struct_0(B_462)
      | ~ l1_pre_topc(A_461)
      | ~ v2_pre_topc(A_461)
      | v2_struct_0(A_461) ) ),
    inference(resolution,[status(thm)],[c_593,c_28])).

tff(c_633,plain,(
    ! [A_464,B_465,C_466] :
      ( r2_hidden('#skF_2'(A_464,B_465,C_466),C_466)
      | k10_yellow_6(A_464,B_465) = C_466
      | ~ m1_subset_1(C_466,k1_zfmisc_1(u1_struct_0(A_464)))
      | r2_hidden('#skF_2'(A_464,B_465,C_466),k10_yellow_6(A_464,B_465))
      | ~ m1_subset_1('#skF_2'(A_464,B_465,C_466),u1_struct_0(A_464))
      | ~ l1_waybel_0(B_465,A_464)
      | ~ v7_waybel_0(B_465)
      | ~ v4_orders_2(B_465)
      | v2_struct_0(B_465)
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464)
      | v2_struct_0(A_464) ) ),
    inference(resolution,[status(thm)],[c_32,c_613])).

tff(c_54,plain,(
    ! [A_139,B_143,C_145] :
      ( r3_waybel_9(A_139,B_143,C_145)
      | ~ r2_hidden(C_145,k10_yellow_6(A_139,B_143))
      | ~ m1_subset_1(C_145,u1_struct_0(A_139))
      | ~ l1_waybel_0(B_143,A_139)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_681,plain,(
    ! [A_471,B_472,C_473] :
      ( r3_waybel_9(A_471,B_472,'#skF_2'(A_471,B_472,C_473))
      | r2_hidden('#skF_2'(A_471,B_472,C_473),C_473)
      | k10_yellow_6(A_471,B_472) = C_473
      | ~ m1_subset_1(C_473,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ m1_subset_1('#skF_2'(A_471,B_472,C_473),u1_struct_0(A_471))
      | ~ l1_waybel_0(B_472,A_471)
      | ~ v7_waybel_0(B_472)
      | ~ v4_orders_2(B_472)
      | v2_struct_0(B_472)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_633,c_54])).

tff(c_685,plain,(
    ! [A_474,B_475,C_476] :
      ( r3_waybel_9(A_474,B_475,'#skF_2'(A_474,B_475,C_476))
      | r2_hidden('#skF_2'(A_474,B_475,C_476),C_476)
      | k10_yellow_6(A_474,B_475) = C_476
      | ~ m1_subset_1(C_476,k1_zfmisc_1(u1_struct_0(A_474)))
      | ~ l1_waybel_0(B_475,A_474)
      | ~ v7_waybel_0(B_475)
      | ~ v4_orders_2(B_475)
      | v2_struct_0(B_475)
      | ~ l1_pre_topc(A_474)
      | ~ v2_pre_topc(A_474)
      | v2_struct_0(A_474) ) ),
    inference(resolution,[status(thm)],[c_12,c_681])).

tff(c_693,plain,(
    ! [A_477,B_478] :
      ( r3_waybel_9(A_477,B_478,'#skF_2'(A_477,B_478,k1_xboole_0))
      | r2_hidden('#skF_2'(A_477,B_478,k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_477,B_478) = k1_xboole_0
      | ~ l1_waybel_0(B_478,A_477)
      | ~ v7_waybel_0(B_478)
      | ~ v4_orders_2(B_478)
      | v2_struct_0(B_478)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477) ) ),
    inference(resolution,[status(thm)],[c_4,c_685])).

tff(c_60,plain,(
    ! [A_160,C_170] :
      ( ~ r3_waybel_9(A_160,'#skF_7'(A_160),C_170)
      | ~ m1_subset_1(C_170,u1_struct_0(A_160))
      | v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_749,plain,(
    ! [A_481] :
      ( ~ m1_subset_1('#skF_2'(A_481,'#skF_7'(A_481),k1_xboole_0),u1_struct_0(A_481))
      | v1_compts_1(A_481)
      | r2_hidden('#skF_2'(A_481,'#skF_7'(A_481),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_481,'#skF_7'(A_481)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(A_481),A_481)
      | ~ v7_waybel_0('#skF_7'(A_481))
      | ~ v4_orders_2('#skF_7'(A_481))
      | v2_struct_0('#skF_7'(A_481))
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_693,c_60])).

tff(c_753,plain,(
    ! [A_9] :
      ( v1_compts_1(A_9)
      | r2_hidden('#skF_2'(A_9,'#skF_7'(A_9),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_9,'#skF_7'(A_9)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0('#skF_7'(A_9),A_9)
      | ~ v7_waybel_0('#skF_7'(A_9))
      | ~ v4_orders_2('#skF_7'(A_9))
      | v2_struct_0('#skF_7'(A_9))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_749])).

tff(c_757,plain,(
    ! [A_482] :
      ( v1_compts_1(A_482)
      | r2_hidden('#skF_2'(A_482,'#skF_7'(A_482),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_482,'#skF_7'(A_482)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(A_482),A_482)
      | ~ v7_waybel_0('#skF_7'(A_482))
      | ~ v4_orders_2('#skF_7'(A_482))
      | v2_struct_0('#skF_7'(A_482))
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_753])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_762,plain,(
    ! [A_482] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_2'(A_482,'#skF_7'(A_482),k1_xboole_0))
      | v1_compts_1(A_482)
      | k10_yellow_6(A_482,'#skF_7'(A_482)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(A_482),A_482)
      | ~ v7_waybel_0('#skF_7'(A_482))
      | ~ v4_orders_2('#skF_7'(A_482))
      | v2_struct_0('#skF_7'(A_482))
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_757,c_8])).

tff(c_767,plain,(
    ! [A_483] :
      ( v1_compts_1(A_483)
      | k10_yellow_6(A_483,'#skF_7'(A_483)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(A_483),A_483)
      | ~ v7_waybel_0('#skF_7'(A_483))
      | ~ v4_orders_2('#skF_7'(A_483))
      | v2_struct_0('#skF_7'(A_483))
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_762])).

tff(c_772,plain,(
    ! [A_484] :
      ( k10_yellow_6(A_484,'#skF_7'(A_484)) = k1_xboole_0
      | ~ v7_waybel_0('#skF_7'(A_484))
      | ~ v4_orders_2('#skF_7'(A_484))
      | v2_struct_0('#skF_7'(A_484))
      | v1_compts_1(A_484)
      | ~ l1_pre_topc(A_484)
      | ~ v2_pre_topc(A_484)
      | v2_struct_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_62,c_767])).

tff(c_776,plain,(
    ! [A_485] :
      ( k10_yellow_6(A_485,'#skF_7'(A_485)) = k1_xboole_0
      | ~ v4_orders_2('#skF_7'(A_485))
      | v2_struct_0('#skF_7'(A_485))
      | v1_compts_1(A_485)
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(resolution,[status(thm)],[c_64,c_772])).

tff(c_797,plain,(
    ! [A_490] :
      ( k10_yellow_6(A_490,'#skF_7'(A_490)) = k1_xboole_0
      | v2_struct_0('#skF_7'(A_490))
      | v1_compts_1(A_490)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_66,c_776])).

tff(c_68,plain,(
    ! [A_160] :
      ( ~ v2_struct_0('#skF_7'(A_160))
      | v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_853,plain,(
    ! [A_491] :
      ( k10_yellow_6(A_491,'#skF_7'(A_491)) = k1_xboole_0
      | v1_compts_1(A_491)
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(resolution,[status(thm)],[c_797,c_68])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_130,plain,(
    ! [B_190] :
      ( v1_compts_1('#skF_10')
      | m2_yellow_6('#skF_12'(B_190),'#skF_10',B_190)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_159,plain,(
    ! [B_190] :
      ( m2_yellow_6('#skF_12'(B_190),'#skF_10',B_190)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_130])).

tff(c_163,plain,(
    ! [C_218,A_219,B_220] :
      ( ~ v2_struct_0(C_218)
      | ~ m2_yellow_6(C_218,A_219,B_220)
      | ~ l1_waybel_0(B_220,A_219)
      | ~ v7_waybel_0(B_220)
      | ~ v4_orders_2(B_220)
      | v2_struct_0(B_220)
      | ~ l1_struct_0(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_166,plain,(
    ! [B_190] :
      ( ~ v2_struct_0('#skF_12'(B_190))
      | ~ l1_struct_0('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_159,c_163])).

tff(c_169,plain,(
    ! [B_190] :
      ( ~ v2_struct_0('#skF_12'(B_190))
      | ~ l1_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_166])).

tff(c_170,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_173,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_173])).

tff(c_179,plain,(
    l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_368,plain,(
    ! [A_317,B_318,D_319] :
      ( m1_connsp_2('#skF_1'(A_317,B_318,k10_yellow_6(A_317,B_318),D_319),A_317,D_319)
      | r2_hidden(D_319,k10_yellow_6(A_317,B_318))
      | ~ m1_subset_1(D_319,u1_struct_0(A_317))
      | ~ l1_waybel_0(B_318,A_317)
      | ~ v7_waybel_0(B_318)
      | ~ v4_orders_2(B_318)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_32,c_364])).

tff(c_48,plain,(
    ! [A_117,B_129,D_138,C_135] :
      ( r2_waybel_0(A_117,B_129,D_138)
      | ~ m1_connsp_2(D_138,A_117,C_135)
      | ~ r3_waybel_9(A_117,B_129,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_117))
      | ~ l1_waybel_0(B_129,A_117)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_403,plain,(
    ! [A_341,B_342,B_343,D_344] :
      ( r2_waybel_0(A_341,B_342,'#skF_1'(A_341,B_343,k10_yellow_6(A_341,B_343),D_344))
      | ~ r3_waybel_9(A_341,B_342,D_344)
      | ~ l1_waybel_0(B_342,A_341)
      | v2_struct_0(B_342)
      | r2_hidden(D_344,k10_yellow_6(A_341,B_343))
      | ~ m1_subset_1(D_344,u1_struct_0(A_341))
      | ~ l1_waybel_0(B_343,A_341)
      | ~ v7_waybel_0(B_343)
      | ~ v4_orders_2(B_343)
      | v2_struct_0(B_343)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_368,c_48])).

tff(c_42,plain,(
    ! [A_99,B_107,D_113,C_111] :
      ( r2_waybel_0(A_99,B_107,D_113)
      | ~ r2_waybel_0(A_99,C_111,D_113)
      | ~ m2_yellow_6(C_111,A_99,B_107)
      | ~ l1_waybel_0(B_107,A_99)
      | ~ v7_waybel_0(B_107)
      | ~ v4_orders_2(B_107)
      | v2_struct_0(B_107)
      | ~ l1_struct_0(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_482,plain,(
    ! [D_409,B_410,A_408,B_407,B_406] :
      ( r2_waybel_0(A_408,B_410,'#skF_1'(A_408,B_407,k10_yellow_6(A_408,B_407),D_409))
      | ~ m2_yellow_6(B_406,A_408,B_410)
      | ~ l1_waybel_0(B_410,A_408)
      | ~ v7_waybel_0(B_410)
      | ~ v4_orders_2(B_410)
      | v2_struct_0(B_410)
      | ~ l1_struct_0(A_408)
      | ~ r3_waybel_9(A_408,B_406,D_409)
      | ~ l1_waybel_0(B_406,A_408)
      | v2_struct_0(B_406)
      | r2_hidden(D_409,k10_yellow_6(A_408,B_407))
      | ~ m1_subset_1(D_409,u1_struct_0(A_408))
      | ~ l1_waybel_0(B_407,A_408)
      | ~ v7_waybel_0(B_407)
      | ~ v4_orders_2(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_403,c_42])).

tff(c_486,plain,(
    ! [B_190,B_407,D_409] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_1'('#skF_10',B_407,k10_yellow_6('#skF_10',B_407),D_409))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),D_409)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r2_hidden(D_409,k10_yellow_6('#skF_10',B_407))
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_407,'#skF_10')
      | ~ v7_waybel_0(B_407)
      | ~ v4_orders_2(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_159,c_482])).

tff(c_490,plain,(
    ! [B_190,B_407,D_409] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_1'('#skF_10',B_407,k10_yellow_6('#skF_10',B_407),D_409))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),D_409)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r2_hidden(D_409,k10_yellow_6('#skF_10',B_407))
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_407,'#skF_10')
      | ~ v7_waybel_0(B_407)
      | ~ v4_orders_2(B_407)
      | v2_struct_0(B_407)
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_179,c_486])).

tff(c_491,plain,(
    ! [B_190,B_407,D_409] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_1'('#skF_10',B_407,k10_yellow_6('#skF_10',B_407),D_409))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),D_409)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r2_hidden(D_409,k10_yellow_6('#skF_10',B_407))
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_407,'#skF_10')
      | ~ v7_waybel_0(B_407)
      | ~ v4_orders_2(B_407)
      | v2_struct_0(B_407)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_490])).

tff(c_880,plain,(
    ! [B_190,D_409] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_1'('#skF_10','#skF_7'('#skF_10'),k1_xboole_0,D_409))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),D_409)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r2_hidden(D_409,k10_yellow_6('#skF_10','#skF_7'('#skF_10')))
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
      | ~ v7_waybel_0('#skF_7'('#skF_10'))
      | ~ v4_orders_2('#skF_7'('#skF_10'))
      | v2_struct_0('#skF_7'('#skF_10'))
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_491])).

tff(c_906,plain,(
    ! [B_190,D_409] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_1'('#skF_10','#skF_7'('#skF_10'),k1_xboole_0,D_409))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),D_409)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r2_hidden(D_409,k10_yellow_6('#skF_10','#skF_7'('#skF_10')))
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
      | ~ v7_waybel_0('#skF_7'('#skF_10'))
      | ~ v4_orders_2('#skF_7'('#skF_10'))
      | v2_struct_0('#skF_7'('#skF_10'))
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | v1_compts_1('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_880])).

tff(c_907,plain,(
    ! [B_190,D_409] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_1'('#skF_10','#skF_7'('#skF_10'),k1_xboole_0,D_409))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),D_409)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r2_hidden(D_409,k10_yellow_6('#skF_10','#skF_7'('#skF_10')))
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
      | ~ v7_waybel_0('#skF_7'('#skF_10'))
      | ~ v4_orders_2('#skF_7'('#skF_10'))
      | v2_struct_0('#skF_7'('#skF_10'))
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_906])).

tff(c_1578,plain,(
    ~ v4_orders_2('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_907])).

tff(c_1581,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1578])).

tff(c_1584,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1581])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1584])).

tff(c_1588,plain,(
    v4_orders_2('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_199,plain,(
    ! [C_230,A_231,B_232] :
      ( l1_waybel_0(C_230,A_231)
      | ~ m2_yellow_6(C_230,A_231,B_232)
      | ~ l1_waybel_0(B_232,A_231)
      | ~ v7_waybel_0(B_232)
      | ~ v4_orders_2(B_232)
      | v2_struct_0(B_232)
      | ~ l1_struct_0(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_202,plain,(
    ! [B_190] :
      ( l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ l1_struct_0('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_159,c_199])).

tff(c_205,plain,(
    ! [B_190] :
      ( l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_202])).

tff(c_206,plain,(
    ! [B_190] :
      ( l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_205])).

tff(c_181,plain,(
    ! [C_222,A_223,B_224] :
      ( v4_orders_2(C_222)
      | ~ m2_yellow_6(C_222,A_223,B_224)
      | ~ l1_waybel_0(B_224,A_223)
      | ~ v7_waybel_0(B_224)
      | ~ v4_orders_2(B_224)
      | v2_struct_0(B_224)
      | ~ l1_struct_0(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_184,plain,(
    ! [B_190] :
      ( v4_orders_2('#skF_12'(B_190))
      | ~ l1_struct_0('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_159,c_181])).

tff(c_187,plain,(
    ! [B_190] :
      ( v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_184])).

tff(c_188,plain,(
    ! [B_190] :
      ( v4_orders_2('#skF_12'(B_190))
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_187])).

tff(c_52,plain,(
    ! [A_117,B_129,C_135] :
      ( m1_connsp_2('#skF_4'(A_117,B_129,C_135),A_117,C_135)
      | r3_waybel_9(A_117,B_129,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_117))
      | ~ l1_waybel_0(B_129,A_117)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_262,plain,(
    ! [A_262,B_263,D_264,C_265] :
      ( r2_waybel_0(A_262,B_263,D_264)
      | ~ m1_connsp_2(D_264,A_262,C_265)
      | ~ r3_waybel_9(A_262,B_263,C_265)
      | ~ m1_subset_1(C_265,u1_struct_0(A_262))
      | ~ l1_waybel_0(B_263,A_262)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_342,plain,(
    ! [A_297,B_298,B_299,C_300] :
      ( r2_waybel_0(A_297,B_298,'#skF_4'(A_297,B_299,C_300))
      | ~ r3_waybel_9(A_297,B_298,C_300)
      | ~ l1_waybel_0(B_298,A_297)
      | v2_struct_0(B_298)
      | r3_waybel_9(A_297,B_299,C_300)
      | ~ m1_subset_1(C_300,u1_struct_0(A_297))
      | ~ l1_waybel_0(B_299,A_297)
      | v2_struct_0(B_299)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_52,c_262])).

tff(c_424,plain,(
    ! [B_372,B_370,A_371,C_369,B_373] :
      ( r2_waybel_0(A_371,B_373,'#skF_4'(A_371,B_370,C_369))
      | ~ m2_yellow_6(B_372,A_371,B_373)
      | ~ l1_waybel_0(B_373,A_371)
      | ~ v7_waybel_0(B_373)
      | ~ v4_orders_2(B_373)
      | v2_struct_0(B_373)
      | ~ l1_struct_0(A_371)
      | ~ r3_waybel_9(A_371,B_372,C_369)
      | ~ l1_waybel_0(B_372,A_371)
      | v2_struct_0(B_372)
      | r3_waybel_9(A_371,B_370,C_369)
      | ~ m1_subset_1(C_369,u1_struct_0(A_371))
      | ~ l1_waybel_0(B_370,A_371)
      | v2_struct_0(B_370)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_342,c_42])).

tff(c_428,plain,(
    ! [B_190,B_370,C_369] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,C_369))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),C_369)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r3_waybel_9('#skF_10',B_370,C_369)
      | ~ m1_subset_1(C_369,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_159,c_424])).

tff(c_432,plain,(
    ! [B_190,B_370,C_369] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,C_369))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),C_369)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r3_waybel_9('#skF_10',B_370,C_369)
      | ~ m1_subset_1(C_369,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_179,c_428])).

tff(c_433,plain,(
    ! [B_190,B_370,C_369] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,C_369))
      | ~ r3_waybel_9('#skF_10','#skF_12'(B_190),C_369)
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | v2_struct_0('#skF_12'(B_190))
      | r3_waybel_9('#skF_10',B_370,C_369)
      | ~ m1_subset_1(C_369,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_432])).

tff(c_707,plain,(
    ! [B_190,B_370] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0)))
      | r3_waybel_9('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_190)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_190))
      | ~ v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_12'(B_190))
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_693,c_433])).

tff(c_730,plain,(
    ! [B_190,B_370] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0)))
      | r3_waybel_9('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_190)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_190))
      | ~ v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_12'(B_190))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_707])).

tff(c_734,plain,(
    ! [B_479,B_480] :
      ( r2_waybel_0('#skF_10',B_479,'#skF_4'('#skF_10',B_480,'#skF_2'('#skF_10','#skF_12'(B_479),k1_xboole_0)))
      | r3_waybel_9('#skF_10',B_480,'#skF_2'('#skF_10','#skF_12'(B_479),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_479),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_480,'#skF_10')
      | v2_struct_0(B_480)
      | ~ l1_waybel_0(B_479,'#skF_10')
      | ~ v7_waybel_0(B_479)
      | ~ v4_orders_2(B_479)
      | v2_struct_0(B_479)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_479),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_479)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_479),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_479))
      | ~ v4_orders_2('#skF_12'(B_479))
      | v2_struct_0('#skF_12'(B_479)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_730])).

tff(c_50,plain,(
    ! [A_117,B_129,C_135] :
      ( ~ r2_waybel_0(A_117,B_129,'#skF_4'(A_117,B_129,C_135))
      | r3_waybel_9(A_117,B_129,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_117))
      | ~ l1_waybel_0(B_129,A_117)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_738,plain,(
    ! [B_480] :
      ( ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | r3_waybel_9('#skF_10',B_480,'#skF_2'('#skF_10','#skF_12'(B_480),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_480),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_480,'#skF_10')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_480),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_480)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_480),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_480))
      | ~ v4_orders_2('#skF_12'(B_480))
      | v2_struct_0('#skF_12'(B_480)) ) ),
    inference(resolution,[status(thm)],[c_734,c_50])).

tff(c_743,plain,(
    ! [B_480] :
      ( v2_struct_0('#skF_10')
      | r3_waybel_9('#skF_10',B_480,'#skF_2'('#skF_10','#skF_12'(B_480),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_480),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_480,'#skF_10')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_480),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_480)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_480),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_480))
      | ~ v4_orders_2('#skF_12'(B_480))
      | v2_struct_0('#skF_12'(B_480)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_738])).

tff(c_910,plain,(
    ! [B_492] :
      ( r3_waybel_9('#skF_10',B_492,'#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_492,'#skF_10')
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_492)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_492),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_492))
      | ~ v4_orders_2('#skF_12'(B_492))
      | v2_struct_0('#skF_12'(B_492)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_743])).

tff(c_913,plain,(
    ! [B_492] :
      ( r3_waybel_9('#skF_10',B_492,'#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0))
      | ~ l1_waybel_0(B_492,'#skF_10')
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_492)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_10')))
      | ~ l1_waybel_0('#skF_12'(B_492),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_492))
      | ~ v4_orders_2('#skF_12'(B_492))
      | v2_struct_0('#skF_12'(B_492))
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_12,c_910])).

tff(c_916,plain,(
    ! [B_492] :
      ( r3_waybel_9('#skF_10',B_492,'#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0))
      | ~ l1_waybel_0(B_492,'#skF_10')
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_492),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_492)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_492),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_492))
      | ~ v4_orders_2('#skF_12'(B_492))
      | v2_struct_0('#skF_12'(B_492))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_4,c_913])).

tff(c_1034,plain,(
    ! [B_508] :
      ( r3_waybel_9('#skF_10',B_508,'#skF_2'('#skF_10','#skF_12'(B_508),k1_xboole_0))
      | ~ l1_waybel_0(B_508,'#skF_10')
      | ~ v7_waybel_0(B_508)
      | ~ v4_orders_2(B_508)
      | v2_struct_0(B_508)
      | r2_hidden('#skF_2'('#skF_10','#skF_12'(B_508),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_10','#skF_12'(B_508)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_508),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_508))
      | ~ v4_orders_2('#skF_12'(B_508))
      | v2_struct_0('#skF_12'(B_508)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_916])).

tff(c_1054,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | r2_hidden('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),k1_xboole_0)
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | ~ v4_orders_2('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1034,c_60])).

tff(c_1076,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | r2_hidden('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),k1_xboole_0)
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | ~ v4_orders_2('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1054])).

tff(c_1077,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | r2_hidden('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),k1_xboole_0)
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | ~ v4_orders_2('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1076])).

tff(c_1398,plain,(
    ~ v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_1077])).

tff(c_1402,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_188,c_1398])).

tff(c_1403,plain,(
    ~ v4_orders_2('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1402])).

tff(c_1406,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1403])).

tff(c_1409,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1406])).

tff(c_1411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1409])).

tff(c_1412,plain,
    ( ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1402])).

tff(c_1414,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1412])).

tff(c_1439,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_1414])).

tff(c_1442,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1439])).

tff(c_1444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1442])).

tff(c_1445,plain,
    ( ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_1447,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1445])).

tff(c_1451,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_1447])).

tff(c_1454,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1451])).

tff(c_1456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1454])).

tff(c_1457,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1445])).

tff(c_1461,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_1457,c_68])).

tff(c_1464,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1461])).

tff(c_1466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1464])).

tff(c_1468,plain,(
    v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1077])).

tff(c_190,plain,(
    ! [C_226,A_227,B_228] :
      ( v7_waybel_0(C_226)
      | ~ m2_yellow_6(C_226,A_227,B_228)
      | ~ l1_waybel_0(B_228,A_227)
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228)
      | ~ l1_struct_0(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_193,plain,(
    ! [B_190] :
      ( v7_waybel_0('#skF_12'(B_190))
      | ~ l1_struct_0('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_159,c_190])).

tff(c_196,plain,(
    ! [B_190] :
      ( v7_waybel_0('#skF_12'(B_190))
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_193])).

tff(c_197,plain,(
    ! [B_190] :
      ( v7_waybel_0('#skF_12'(B_190))
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_196])).

tff(c_1186,plain,(
    ! [C_519,A_520,B_521] :
      ( ~ r1_tarski(C_519,'#skF_2'(A_520,B_521,C_519))
      | k10_yellow_6(A_520,B_521) = C_519
      | ~ m1_subset_1(C_519,k1_zfmisc_1(u1_struct_0(A_520)))
      | r2_hidden('#skF_2'(A_520,B_521,C_519),k10_yellow_6(A_520,B_521))
      | ~ m1_subset_1('#skF_2'(A_520,B_521,C_519),u1_struct_0(A_520))
      | ~ l1_waybel_0(B_521,A_520)
      | ~ v7_waybel_0(B_521)
      | ~ v4_orders_2(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_520)
      | ~ v2_pre_topc(A_520)
      | v2_struct_0(A_520) ) ),
    inference(resolution,[status(thm)],[c_633,c_8])).

tff(c_1189,plain,(
    ! [A_520,B_521] :
      ( k10_yellow_6(A_520,B_521) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_520)))
      | r2_hidden('#skF_2'(A_520,B_521,k1_xboole_0),k10_yellow_6(A_520,B_521))
      | ~ m1_subset_1('#skF_2'(A_520,B_521,k1_xboole_0),u1_struct_0(A_520))
      | ~ l1_waybel_0(B_521,A_520)
      | ~ v7_waybel_0(B_521)
      | ~ v4_orders_2(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_520)
      | ~ v2_pre_topc(A_520)
      | v2_struct_0(A_520) ) ),
    inference(resolution,[status(thm)],[c_2,c_1186])).

tff(c_1193,plain,(
    ! [A_522,B_523] :
      ( k10_yellow_6(A_522,B_523) = k1_xboole_0
      | r2_hidden('#skF_2'(A_522,B_523,k1_xboole_0),k10_yellow_6(A_522,B_523))
      | ~ m1_subset_1('#skF_2'(A_522,B_523,k1_xboole_0),u1_struct_0(A_522))
      | ~ l1_waybel_0(B_523,A_522)
      | ~ v7_waybel_0(B_523)
      | ~ v4_orders_2(B_523)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_522)
      | ~ v2_pre_topc(A_522)
      | v2_struct_0(A_522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1189])).

tff(c_1299,plain,(
    ! [A_529,B_530] :
      ( r3_waybel_9(A_529,B_530,'#skF_2'(A_529,B_530,k1_xboole_0))
      | k10_yellow_6(A_529,B_530) = k1_xboole_0
      | ~ m1_subset_1('#skF_2'(A_529,B_530,k1_xboole_0),u1_struct_0(A_529))
      | ~ l1_waybel_0(B_530,A_529)
      | ~ v7_waybel_0(B_530)
      | ~ v4_orders_2(B_530)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc(A_529)
      | ~ v2_pre_topc(A_529)
      | v2_struct_0(A_529) ) ),
    inference(resolution,[status(thm)],[c_1193,c_54])).

tff(c_1302,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_1299])).

tff(c_1334,plain,(
    ! [A_536,B_537] :
      ( r3_waybel_9(A_536,B_537,'#skF_2'(A_536,B_537,k1_xboole_0))
      | k10_yellow_6(A_536,B_537) = k1_xboole_0
      | ~ l1_waybel_0(B_537,A_536)
      | ~ v7_waybel_0(B_537)
      | ~ v4_orders_2(B_537)
      | v2_struct_0(B_537)
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1302])).

tff(c_1350,plain,(
    ! [B_190,B_370] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0)))
      | r3_waybel_9('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | k10_yellow_6('#skF_10','#skF_12'(B_190)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_190))
      | ~ v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_12'(B_190))
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1334,c_433])).

tff(c_1376,plain,(
    ! [B_190,B_370] :
      ( r2_waybel_0('#skF_10',B_190,'#skF_4'('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0)))
      | r3_waybel_9('#skF_10',B_370,'#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_190),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_370,'#skF_10')
      | v2_struct_0(B_370)
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | k10_yellow_6('#skF_10','#skF_12'(B_190)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_190))
      | ~ v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_12'(B_190))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1350])).

tff(c_1741,plain,(
    ! [B_592,B_593] :
      ( r2_waybel_0('#skF_10',B_592,'#skF_4'('#skF_10',B_593,'#skF_2'('#skF_10','#skF_12'(B_592),k1_xboole_0)))
      | r3_waybel_9('#skF_10',B_593,'#skF_2'('#skF_10','#skF_12'(B_592),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_592),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_593,'#skF_10')
      | v2_struct_0(B_593)
      | ~ l1_waybel_0(B_592,'#skF_10')
      | ~ v7_waybel_0(B_592)
      | ~ v4_orders_2(B_592)
      | v2_struct_0(B_592)
      | k10_yellow_6('#skF_10','#skF_12'(B_592)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_592),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_592))
      | ~ v4_orders_2('#skF_12'(B_592))
      | v2_struct_0('#skF_12'(B_592)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1376])).

tff(c_1745,plain,(
    ! [B_593] :
      ( ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | r3_waybel_9('#skF_10',B_593,'#skF_2'('#skF_10','#skF_12'(B_593),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_593),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_593,'#skF_10')
      | ~ v7_waybel_0(B_593)
      | ~ v4_orders_2(B_593)
      | v2_struct_0(B_593)
      | k10_yellow_6('#skF_10','#skF_12'(B_593)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_593),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_593))
      | ~ v4_orders_2('#skF_12'(B_593))
      | v2_struct_0('#skF_12'(B_593)) ) ),
    inference(resolution,[status(thm)],[c_1741,c_50])).

tff(c_1750,plain,(
    ! [B_593] :
      ( v2_struct_0('#skF_10')
      | r3_waybel_9('#skF_10',B_593,'#skF_2'('#skF_10','#skF_12'(B_593),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_593),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_593,'#skF_10')
      | ~ v7_waybel_0(B_593)
      | ~ v4_orders_2(B_593)
      | v2_struct_0(B_593)
      | k10_yellow_6('#skF_10','#skF_12'(B_593)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_593),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_593))
      | ~ v4_orders_2('#skF_12'(B_593))
      | v2_struct_0('#skF_12'(B_593)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1745])).

tff(c_1764,plain,(
    ! [B_596] :
      ( r3_waybel_9('#skF_10',B_596,'#skF_2'('#skF_10','#skF_12'(B_596),k1_xboole_0))
      | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'(B_596),k1_xboole_0),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0(B_596,'#skF_10')
      | ~ v7_waybel_0(B_596)
      | ~ v4_orders_2(B_596)
      | v2_struct_0(B_596)
      | k10_yellow_6('#skF_10','#skF_12'(B_596)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_596),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_596))
      | ~ v4_orders_2('#skF_12'(B_596))
      | v2_struct_0('#skF_12'(B_596)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1750])).

tff(c_1767,plain,(
    ! [B_596] :
      ( r3_waybel_9('#skF_10',B_596,'#skF_2'('#skF_10','#skF_12'(B_596),k1_xboole_0))
      | ~ l1_waybel_0(B_596,'#skF_10')
      | ~ v7_waybel_0(B_596)
      | ~ v4_orders_2(B_596)
      | v2_struct_0(B_596)
      | k10_yellow_6('#skF_10','#skF_12'(B_596)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_10')))
      | ~ l1_waybel_0('#skF_12'(B_596),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_596))
      | ~ v4_orders_2('#skF_12'(B_596))
      | v2_struct_0('#skF_12'(B_596))
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_12,c_1764])).

tff(c_1770,plain,(
    ! [B_596] :
      ( r3_waybel_9('#skF_10',B_596,'#skF_2'('#skF_10','#skF_12'(B_596),k1_xboole_0))
      | ~ l1_waybel_0(B_596,'#skF_10')
      | ~ v7_waybel_0(B_596)
      | ~ v4_orders_2(B_596)
      | v2_struct_0(B_596)
      | k10_yellow_6('#skF_10','#skF_12'(B_596)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_596),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_596))
      | ~ v4_orders_2('#skF_12'(B_596))
      | v2_struct_0('#skF_12'(B_596))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_4,c_1767])).

tff(c_1772,plain,(
    ! [B_597] :
      ( r3_waybel_9('#skF_10',B_597,'#skF_2'('#skF_10','#skF_12'(B_597),k1_xboole_0))
      | ~ l1_waybel_0(B_597,'#skF_10')
      | ~ v7_waybel_0(B_597)
      | ~ v4_orders_2(B_597)
      | v2_struct_0(B_597)
      | k10_yellow_6('#skF_10','#skF_12'(B_597)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_597),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_597))
      | ~ v4_orders_2('#skF_12'(B_597))
      | v2_struct_0('#skF_12'(B_597)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1770])).

tff(c_1792,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | ~ v4_orders_2('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1772,c_60])).

tff(c_1814,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1588,c_92,c_90,c_1792])).

tff(c_1815,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1814])).

tff(c_1820,plain,(
    ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_1815])).

tff(c_1823,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_197,c_1820])).

tff(c_1826,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1823])).

tff(c_1832,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1826])).

tff(c_1835,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_1832])).

tff(c_1838,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1835])).

tff(c_1840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1838])).

tff(c_1841,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1826])).

tff(c_1850,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1841])).

tff(c_1853,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_1850])).

tff(c_1856,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1853])).

tff(c_1858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1856])).

tff(c_1859,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1841])).

tff(c_1863,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_1859,c_68])).

tff(c_1866,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1863])).

tff(c_1868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1866])).

tff(c_1870,plain,(
    v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1815])).

tff(c_1869,plain,
    ( ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10'))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1815])).

tff(c_1876,plain,(
    ~ m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1869])).

tff(c_1879,plain,
    ( k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_10')))
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | ~ v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))
    | ~ v4_orders_2('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_12,c_1876])).

tff(c_1882,plain,
    ( k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1468,c_1870,c_4,c_1879])).

tff(c_1883,plain,
    ( k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1882])).

tff(c_1884,plain,(
    ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1883])).

tff(c_1952,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_206,c_1884])).

tff(c_1955,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1952])).

tff(c_1956,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_1959,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_1956])).

tff(c_1962,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1959])).

tff(c_1964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1962])).

tff(c_1965,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_1979,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1965])).

tff(c_1982,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_1979])).

tff(c_1985,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1982])).

tff(c_1987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1985])).

tff(c_1988,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1965])).

tff(c_1992,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_1988,c_68])).

tff(c_1995,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1992])).

tff(c_1997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_1995])).

tff(c_1998,plain,
    ( v2_struct_0('#skF_12'('#skF_7'('#skF_10')))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1883])).

tff(c_2199,plain,(
    k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1998])).

tff(c_118,plain,(
    ! [B_190] :
      ( v1_compts_1('#skF_10')
      | v3_yellow_6('#skF_12'(B_190),'#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_145,plain,(
    ! [B_190] :
      ( v3_yellow_6('#skF_12'(B_190),'#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_118])).

tff(c_208,plain,(
    ! [A_234,B_235] :
      ( k10_yellow_6(A_234,B_235) != k1_xboole_0
      | ~ v3_yellow_6(B_235,A_234)
      | ~ l1_waybel_0(B_235,A_234)
      | ~ v7_waybel_0(B_235)
      | ~ v4_orders_2(B_235)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_211,plain,(
    ! [B_190] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_190)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_190))
      | ~ v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_12'(B_190))
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_145,c_208])).

tff(c_214,plain,(
    ! [B_190] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_190)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_190),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_190))
      | ~ v4_orders_2('#skF_12'(B_190))
      | v2_struct_0('#skF_12'(B_190))
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_211])).

tff(c_239,plain,(
    ! [B_251] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_251)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_12'(B_251),'#skF_10')
      | ~ v7_waybel_0('#skF_12'(B_251))
      | ~ v4_orders_2('#skF_12'(B_251))
      | v2_struct_0('#skF_12'(B_251))
      | ~ l1_waybel_0(B_251,'#skF_10')
      | ~ v7_waybel_0(B_251)
      | ~ v4_orders_2(B_251)
      | v2_struct_0(B_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_214])).

tff(c_244,plain,(
    ! [B_252] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_252)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_12'(B_252))
      | ~ v4_orders_2('#skF_12'(B_252))
      | v2_struct_0('#skF_12'(B_252))
      | ~ l1_waybel_0(B_252,'#skF_10')
      | ~ v7_waybel_0(B_252)
      | ~ v4_orders_2(B_252)
      | v2_struct_0(B_252) ) ),
    inference(resolution,[status(thm)],[c_206,c_239])).

tff(c_249,plain,(
    ! [B_253] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_253)) != k1_xboole_0
      | ~ v4_orders_2('#skF_12'(B_253))
      | v2_struct_0('#skF_12'(B_253))
      | ~ l1_waybel_0(B_253,'#skF_10')
      | ~ v7_waybel_0(B_253)
      | ~ v4_orders_2(B_253)
      | v2_struct_0(B_253) ) ),
    inference(resolution,[status(thm)],[c_197,c_244])).

tff(c_254,plain,(
    ! [B_254] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_254)) != k1_xboole_0
      | v2_struct_0('#skF_12'(B_254))
      | ~ l1_waybel_0(B_254,'#skF_10')
      | ~ v7_waybel_0(B_254)
      | ~ v4_orders_2(B_254)
      | v2_struct_0(B_254) ) ),
    inference(resolution,[status(thm)],[c_188,c_249])).

tff(c_178,plain,(
    ! [B_190] :
      ( ~ v2_struct_0('#skF_12'(B_190))
      | ~ l1_waybel_0(B_190,'#skF_10')
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190) ) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_258,plain,(
    ! [B_254] :
      ( k10_yellow_6('#skF_10','#skF_12'(B_254)) != k1_xboole_0
      | ~ l1_waybel_0(B_254,'#skF_10')
      | ~ v7_waybel_0(B_254)
      | ~ v4_orders_2(B_254)
      | v2_struct_0(B_254) ) ),
    inference(resolution,[status(thm)],[c_254,c_178])).

tff(c_2274,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2199,c_258])).

tff(c_2350,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_2274])).

tff(c_2358,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2350])).

tff(c_2361,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_2358])).

tff(c_2364,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2361])).

tff(c_2366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2364])).

tff(c_2367,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2350])).

tff(c_2376,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2367])).

tff(c_2379,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_2376])).

tff(c_2382,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2379])).

tff(c_2384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2382])).

tff(c_2385,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2367])).

tff(c_2389,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2385,c_68])).

tff(c_2392,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2389])).

tff(c_2394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2392])).

tff(c_2395,plain,(
    v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1998])).

tff(c_2411,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2395,c_178])).

tff(c_2414,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_2411])).

tff(c_2415,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_2426,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_2415])).

tff(c_2429,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2426])).

tff(c_2431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2429])).

tff(c_2432,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_2434,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2432])).

tff(c_2437,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_2434])).

tff(c_2440,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2437])).

tff(c_2442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2440])).

tff(c_2443,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2432])).

tff(c_2447,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2443,c_68])).

tff(c_2450,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2447])).

tff(c_2452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2450])).

tff(c_2454,plain,(
    m1_subset_1('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),u1_struct_0('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_918,plain,(
    ! [A_493,C_494] :
      ( r3_waybel_9(A_493,'#skF_7'(A_493),C_494)
      | ~ r2_hidden(C_494,k1_xboole_0)
      | ~ m1_subset_1(C_494,u1_struct_0(A_493))
      | ~ l1_waybel_0('#skF_7'(A_493),A_493)
      | ~ v7_waybel_0('#skF_7'(A_493))
      | ~ v4_orders_2('#skF_7'(A_493))
      | v2_struct_0('#skF_7'(A_493))
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493)
      | v1_compts_1(A_493)
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_54])).

tff(c_926,plain,(
    ! [C_494,A_493] :
      ( ~ r2_hidden(C_494,k1_xboole_0)
      | ~ m1_subset_1(C_494,u1_struct_0(A_493))
      | ~ l1_waybel_0('#skF_7'(A_493),A_493)
      | ~ v7_waybel_0('#skF_7'(A_493))
      | ~ v4_orders_2('#skF_7'(A_493))
      | v2_struct_0('#skF_7'(A_493))
      | v1_compts_1(A_493)
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(resolution,[status(thm)],[c_918,c_60])).

tff(c_2470,plain,
    ( ~ r2_hidden('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2454,c_926])).

tff(c_2483,plain,
    ( ~ r2_hidden('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10'))
    | v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1588,c_2470])).

tff(c_2484,plain,
    ( ~ r2_hidden('#skF_2'('#skF_10','#skF_12'('#skF_7'('#skF_10')),k1_xboole_0),k1_xboole_0)
    | ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2483])).

tff(c_2508,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2484])).

tff(c_2511,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_2508])).

tff(c_2514,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2511])).

tff(c_2516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2514])).

tff(c_2518,plain,(
    v7_waybel_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2484])).

tff(c_2453,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10'))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_2531,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10'))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_2453])).

tff(c_2532,plain,(
    ~ l1_waybel_0('#skF_12'('#skF_7'('#skF_10')),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2531])).

tff(c_2536,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_206,c_2532])).

tff(c_2539,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_2518,c_2536])).

tff(c_2540,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2539])).

tff(c_2543,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_2540])).

tff(c_2546,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2543])).

tff(c_2548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2546])).

tff(c_2549,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2539])).

tff(c_2553,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2549,c_68])).

tff(c_2556,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2553])).

tff(c_2558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2556])).

tff(c_2559,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2531])).

tff(c_2577,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2559])).

tff(c_2580,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_2577])).

tff(c_2583,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2580])).

tff(c_2585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2583])).

tff(c_2587,plain,(
    l1_waybel_0('#skF_7'('#skF_10'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_2559])).

tff(c_2586,plain,
    ( v2_struct_0('#skF_7'('#skF_10'))
    | k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_2559])).

tff(c_2589,plain,(
    v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_2586])).

tff(c_2592,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2589,c_178])).

tff(c_2595,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_2518,c_2587,c_2592])).

tff(c_2598,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2595,c_68])).

tff(c_2601,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2598])).

tff(c_2603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2601])).

tff(c_2604,plain,
    ( k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2586])).

tff(c_2606,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2604])).

tff(c_2667,plain,
    ( v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2606,c_68])).

tff(c_2670,plain,
    ( v1_compts_1('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2667])).

tff(c_2672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_132,c_2670])).

tff(c_2674,plain,(
    ~ v2_struct_0('#skF_7'('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2604])).

tff(c_2673,plain,(
    k10_yellow_6('#skF_10','#skF_12'('#skF_7'('#skF_10'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2604])).

tff(c_2737,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_10'),'#skF_10')
    | ~ v7_waybel_0('#skF_7'('#skF_10'))
    | ~ v4_orders_2('#skF_7'('#skF_10'))
    | v2_struct_0('#skF_7'('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2673,c_258])).

tff(c_2814,plain,(
    v2_struct_0('#skF_7'('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_2518,c_2587,c_2737])).

tff(c_2816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2674,c_2814])).

tff(c_2817,plain,(
    ~ v2_struct_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_2818,plain,(
    v1_compts_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_102,plain,
    ( v4_orders_2('#skF_11')
    | ~ v1_compts_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_2819,plain,(
    ~ v1_compts_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_2821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_2819])).

tff(c_2822,plain,(
    v4_orders_2('#skF_11') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_100,plain,
    ( v7_waybel_0('#skF_11')
    | ~ v1_compts_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_2827,plain,(
    v7_waybel_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_100])).

tff(c_98,plain,
    ( l1_waybel_0('#skF_11','#skF_10')
    | ~ v1_compts_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_2829,plain,(
    l1_waybel_0('#skF_11','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_98])).

tff(c_70,plain,(
    ! [A_160,B_167] :
      ( r3_waybel_9(A_160,B_167,'#skF_6'(A_160,B_167))
      | ~ l1_waybel_0(B_167,A_160)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_72,plain,(
    ! [A_160,B_167] :
      ( m1_subset_1('#skF_6'(A_160,B_167),u1_struct_0(A_160))
      | ~ l1_waybel_0(B_167,A_160)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_2911,plain,(
    ! [A_711,B_712,C_713] :
      ( m2_yellow_6('#skF_5'(A_711,B_712,C_713),A_711,B_712)
      | ~ r3_waybel_9(A_711,B_712,C_713)
      | ~ m1_subset_1(C_713,u1_struct_0(A_711))
      | ~ l1_waybel_0(B_712,A_711)
      | ~ v7_waybel_0(B_712)
      | ~ v4_orders_2(B_712)
      | v2_struct_0(B_712)
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

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

tff(c_3004,plain,(
    ! [A_731,B_732,C_733] :
      ( l1_waybel_0('#skF_5'(A_731,B_732,C_733),A_731)
      | ~ l1_struct_0(A_731)
      | ~ r3_waybel_9(A_731,B_732,C_733)
      | ~ m1_subset_1(C_733,u1_struct_0(A_731))
      | ~ l1_waybel_0(B_732,A_731)
      | ~ v7_waybel_0(B_732)
      | ~ v4_orders_2(B_732)
      | v2_struct_0(B_732)
      | ~ l1_pre_topc(A_731)
      | ~ v2_pre_topc(A_731)
      | v2_struct_0(A_731) ) ),
    inference(resolution,[status(thm)],[c_2911,c_34])).

tff(c_3064,plain,(
    ! [A_775,B_776,B_777] :
      ( l1_waybel_0('#skF_5'(A_775,B_776,'#skF_6'(A_775,B_777)),A_775)
      | ~ l1_struct_0(A_775)
      | ~ r3_waybel_9(A_775,B_776,'#skF_6'(A_775,B_777))
      | ~ l1_waybel_0(B_776,A_775)
      | ~ v7_waybel_0(B_776)
      | ~ v4_orders_2(B_776)
      | v2_struct_0(B_776)
      | ~ l1_waybel_0(B_777,A_775)
      | ~ v7_waybel_0(B_777)
      | ~ v4_orders_2(B_777)
      | v2_struct_0(B_777)
      | ~ v1_compts_1(A_775)
      | ~ l1_pre_topc(A_775)
      | ~ v2_pre_topc(A_775)
      | v2_struct_0(A_775) ) ),
    inference(resolution,[status(thm)],[c_72,c_3004])).

tff(c_44,plain,(
    ! [B_116,A_114] :
      ( v3_yellow_6(B_116,A_114)
      | k10_yellow_6(A_114,B_116) = k1_xboole_0
      | ~ l1_waybel_0(B_116,A_114)
      | ~ v7_waybel_0(B_116)
      | ~ v4_orders_2(B_116)
      | v2_struct_0(B_116)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_96,plain,(
    ! [C_189] :
      ( ~ v3_yellow_6(C_189,'#skF_10')
      | ~ m2_yellow_6(C_189,'#skF_10','#skF_11')
      | ~ v1_compts_1('#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_2833,plain,(
    ! [C_189] :
      ( ~ v3_yellow_6(C_189,'#skF_10')
      | ~ m2_yellow_6(C_189,'#skF_10','#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_96])).

tff(c_2927,plain,(
    ! [C_713] :
      ( ~ v3_yellow_6('#skF_5'('#skF_10','#skF_11',C_713),'#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11',C_713)
      | ~ m1_subset_1(C_713,u1_struct_0('#skF_10'))
      | ~ l1_waybel_0('#skF_11','#skF_10')
      | ~ v7_waybel_0('#skF_11')
      | ~ v4_orders_2('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2911,c_2833])).

tff(c_2934,plain,(
    ! [C_713] :
      ( ~ v3_yellow_6('#skF_5'('#skF_10','#skF_11',C_713),'#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11',C_713)
      | ~ m1_subset_1(C_713,u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_11')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2822,c_2827,c_2829,c_2927])).

tff(c_2936,plain,(
    ! [C_714] :
      ( ~ v3_yellow_6('#skF_5'('#skF_10','#skF_11',C_714),'#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11',C_714)
      | ~ m1_subset_1(C_714,u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_2934])).

tff(c_2939,plain,(
    ! [C_714] :
      ( ~ r3_waybel_9('#skF_10','#skF_11',C_714)
      | ~ m1_subset_1(C_714,u1_struct_0('#skF_10'))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11',C_714)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_5'('#skF_10','#skF_11',C_714),'#skF_10')
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11',C_714))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11',C_714))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11',C_714))
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_44,c_2936])).

tff(c_2942,plain,(
    ! [C_714] :
      ( ~ r3_waybel_9('#skF_10','#skF_11',C_714)
      | ~ m1_subset_1(C_714,u1_struct_0('#skF_10'))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11',C_714)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_5'('#skF_10','#skF_11',C_714),'#skF_10')
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11',C_714))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11',C_714))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11',C_714))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2939])).

tff(c_2945,plain,(
    ! [C_718] :
      ( ~ r3_waybel_9('#skF_10','#skF_11',C_718)
      | ~ m1_subset_1(C_718,u1_struct_0('#skF_10'))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11',C_718)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_5'('#skF_10','#skF_11',C_718),'#skF_10')
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11',C_718))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11',C_718))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11',C_718)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2942])).

tff(c_2953,plain,(
    ! [B_167] :
      ( ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)),'#skF_10')
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_72,c_2945])).

tff(c_2960,plain,(
    ! [B_167] :
      ( ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)),'#skF_10')
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_2953])).

tff(c_2961,plain,(
    ! [B_167] :
      ( ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)),'#skF_10')
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2960])).

tff(c_3068,plain,(
    ! [B_777] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_777))
      | ~ l1_waybel_0('#skF_11','#skF_10')
      | ~ v7_waybel_0('#skF_11')
      | ~ v4_orders_2('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l1_waybel_0(B_777,'#skF_10')
      | ~ v7_waybel_0(B_777)
      | ~ v4_orders_2(B_777)
      | v2_struct_0(B_777)
      | ~ v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3064,c_2961])).

tff(c_3071,plain,(
    ! [B_777] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_777))
      | v2_struct_0('#skF_11')
      | ~ l1_waybel_0(B_777,'#skF_10')
      | ~ v7_waybel_0(B_777)
      | ~ v4_orders_2(B_777)
      | v2_struct_0(B_777)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_2822,c_2827,c_2829,c_3068])).

tff(c_3072,plain,(
    ! [B_777] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_777)))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_777))
      | ~ l1_waybel_0(B_777,'#skF_10')
      | ~ v7_waybel_0(B_777)
      | ~ v4_orders_2(B_777)
      | v2_struct_0(B_777) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_3071])).

tff(c_3073,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3072])).

tff(c_3076,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_3073])).

tff(c_3080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3076])).

tff(c_3082,plain,(
    l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_3072])).

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

tff(c_2969,plain,(
    ! [A_722,B_723,C_724] :
      ( v4_orders_2('#skF_5'(A_722,B_723,C_724))
      | ~ l1_struct_0(A_722)
      | ~ r3_waybel_9(A_722,B_723,C_724)
      | ~ m1_subset_1(C_724,u1_struct_0(A_722))
      | ~ l1_waybel_0(B_723,A_722)
      | ~ v7_waybel_0(B_723)
      | ~ v4_orders_2(B_723)
      | v2_struct_0(B_723)
      | ~ l1_pre_topc(A_722)
      | ~ v2_pre_topc(A_722)
      | v2_struct_0(A_722) ) ),
    inference(resolution,[status(thm)],[c_2911,c_38])).

tff(c_2975,plain,(
    ! [A_160,B_723,B_167] :
      ( v4_orders_2('#skF_5'(A_160,B_723,'#skF_6'(A_160,B_167)))
      | ~ l1_struct_0(A_160)
      | ~ r3_waybel_9(A_160,B_723,'#skF_6'(A_160,B_167))
      | ~ l1_waybel_0(B_723,A_160)
      | ~ v7_waybel_0(B_723)
      | ~ v4_orders_2(B_723)
      | v2_struct_0(B_723)
      | ~ l1_waybel_0(B_167,A_160)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_72,c_2969])).

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

tff(c_2962,plain,(
    ! [A_719,B_720,C_721] :
      ( v7_waybel_0('#skF_5'(A_719,B_720,C_721))
      | ~ l1_struct_0(A_719)
      | ~ r3_waybel_9(A_719,B_720,C_721)
      | ~ m1_subset_1(C_721,u1_struct_0(A_719))
      | ~ l1_waybel_0(B_720,A_719)
      | ~ v7_waybel_0(B_720)
      | ~ v4_orders_2(B_720)
      | v2_struct_0(B_720)
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719)
      | v2_struct_0(A_719) ) ),
    inference(resolution,[status(thm)],[c_2911,c_36])).

tff(c_2968,plain,(
    ! [A_160,B_720,B_167] :
      ( v7_waybel_0('#skF_5'(A_160,B_720,'#skF_6'(A_160,B_167)))
      | ~ l1_struct_0(A_160)
      | ~ r3_waybel_9(A_160,B_720,'#skF_6'(A_160,B_167))
      | ~ l1_waybel_0(B_720,A_160)
      | ~ v7_waybel_0(B_720)
      | ~ v4_orders_2(B_720)
      | v2_struct_0(B_720)
      | ~ l1_waybel_0(B_167,A_160)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1(A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_72,c_2962])).

tff(c_3106,plain,(
    ! [B_800] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_800))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_800)))
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_800)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_800)))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_800))
      | ~ l1_waybel_0(B_800,'#skF_10')
      | ~ v7_waybel_0(B_800)
      | ~ v4_orders_2(B_800)
      | v2_struct_0(B_800) ) ),
    inference(splitRight,[status(thm)],[c_3072])).

tff(c_3110,plain,(
    ! [B_167] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | ~ l1_waybel_0('#skF_11','#skF_10')
      | ~ v7_waybel_0('#skF_11')
      | ~ v4_orders_2('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2968,c_3106])).

tff(c_3113,plain,(
    ! [B_167] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | v2_struct_0('#skF_11')
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_2822,c_2827,c_2829,c_3082,c_3110])).

tff(c_3115,plain,(
    ! [B_801] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_801))) = k1_xboole_0
      | ~ v4_orders_2('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_801)))
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_801)))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_801))
      | ~ l1_waybel_0(B_801,'#skF_10')
      | ~ v7_waybel_0(B_801)
      | ~ v4_orders_2(B_801)
      | v2_struct_0(B_801) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_3113])).

tff(c_3119,plain,(
    ! [B_167] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ l1_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | ~ l1_waybel_0('#skF_11','#skF_10')
      | ~ v7_waybel_0('#skF_11')
      | ~ v4_orders_2('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2975,c_3115])).

tff(c_3122,plain,(
    ! [B_167] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167)))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | v2_struct_0('#skF_11')
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_2822,c_2827,c_2829,c_3082,c_3119])).

tff(c_3124,plain,(
    ! [B_802] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_802))) = k1_xboole_0
      | v2_struct_0('#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_802)))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_802))
      | ~ l1_waybel_0(B_802,'#skF_10')
      | ~ v7_waybel_0(B_802)
      | ~ v4_orders_2(B_802)
      | v2_struct_0(B_802) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_3122])).

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

tff(c_2929,plain,(
    ! [A_711,B_712,C_713] :
      ( ~ v2_struct_0('#skF_5'(A_711,B_712,C_713))
      | ~ l1_struct_0(A_711)
      | ~ r3_waybel_9(A_711,B_712,C_713)
      | ~ m1_subset_1(C_713,u1_struct_0(A_711))
      | ~ l1_waybel_0(B_712,A_711)
      | ~ v7_waybel_0(B_712)
      | ~ v4_orders_2(B_712)
      | v2_struct_0(B_712)
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(resolution,[status(thm)],[c_2911,c_40])).

tff(c_3126,plain,(
    ! [B_802] :
      ( ~ l1_struct_0('#skF_10')
      | ~ m1_subset_1('#skF_6'('#skF_10',B_802),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0('#skF_11','#skF_10')
      | ~ v7_waybel_0('#skF_11')
      | ~ v4_orders_2('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_802))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_802))
      | ~ l1_waybel_0(B_802,'#skF_10')
      | ~ v7_waybel_0(B_802)
      | ~ v4_orders_2(B_802)
      | v2_struct_0(B_802) ) ),
    inference(resolution,[status(thm)],[c_3124,c_2929])).

tff(c_3129,plain,(
    ! [B_802] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_802),u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_11')
      | v2_struct_0('#skF_10')
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_802))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_802))
      | ~ l1_waybel_0(B_802,'#skF_10')
      | ~ v7_waybel_0(B_802)
      | ~ v4_orders_2(B_802)
      | v2_struct_0(B_802) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2822,c_2827,c_2829,c_3082,c_3126])).

tff(c_3131,plain,(
    ! [B_803] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_803),u1_struct_0('#skF_10'))
      | k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_803))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_803))
      | ~ l1_waybel_0(B_803,'#skF_10')
      | ~ v7_waybel_0(B_803)
      | ~ v4_orders_2(B_803)
      | v2_struct_0(B_803) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_3129])).

tff(c_3135,plain,(
    ! [B_167] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_72,c_3131])).

tff(c_3138,plain,(
    ! [B_167] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_3135])).

tff(c_3140,plain,(
    ! [B_804] :
      ( k10_yellow_6('#skF_10','#skF_5'('#skF_10','#skF_11','#skF_6'('#skF_10',B_804))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_804))
      | ~ l1_waybel_0(B_804,'#skF_10')
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3138])).

tff(c_2976,plain,(
    ! [C_725,A_726,B_727] :
      ( r2_hidden(C_725,k10_yellow_6(A_726,'#skF_5'(A_726,B_727,C_725)))
      | ~ r3_waybel_9(A_726,B_727,C_725)
      | ~ m1_subset_1(C_725,u1_struct_0(A_726))
      | ~ l1_waybel_0(B_727,A_726)
      | ~ v7_waybel_0(B_727)
      | ~ v4_orders_2(B_727)
      | v2_struct_0(B_727)
      | ~ l1_pre_topc(A_726)
      | ~ v2_pre_topc(A_726)
      | v2_struct_0(A_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_2988,plain,(
    ! [A_726,B_727,C_725] :
      ( ~ r1_tarski(k10_yellow_6(A_726,'#skF_5'(A_726,B_727,C_725)),C_725)
      | ~ r3_waybel_9(A_726,B_727,C_725)
      | ~ m1_subset_1(C_725,u1_struct_0(A_726))
      | ~ l1_waybel_0(B_727,A_726)
      | ~ v7_waybel_0(B_727)
      | ~ v4_orders_2(B_727)
      | v2_struct_0(B_727)
      | ~ l1_pre_topc(A_726)
      | ~ v2_pre_topc(A_726)
      | v2_struct_0(A_726) ) ),
    inference(resolution,[status(thm)],[c_2976,c_8])).

tff(c_3154,plain,(
    ! [B_804] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_6'('#skF_10',B_804))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_804))
      | ~ m1_subset_1('#skF_6'('#skF_10',B_804),u1_struct_0('#skF_10'))
      | ~ l1_waybel_0('#skF_11','#skF_10')
      | ~ v7_waybel_0('#skF_11')
      | ~ v4_orders_2('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_804))
      | ~ l1_waybel_0(B_804,'#skF_10')
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3140,c_2988])).

tff(c_3181,plain,(
    ! [B_804] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_804),u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_11')
      | v2_struct_0('#skF_10')
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_804))
      | ~ l1_waybel_0(B_804,'#skF_10')
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2822,c_2827,c_2829,c_2,c_3154])).

tff(c_3196,plain,(
    ! [B_805] :
      ( ~ m1_subset_1('#skF_6'('#skF_10',B_805),u1_struct_0('#skF_10'))
      | ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_805))
      | ~ l1_waybel_0(B_805,'#skF_10')
      | ~ v7_waybel_0(B_805)
      | ~ v4_orders_2(B_805)
      | v2_struct_0(B_805) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_3181])).

tff(c_3200,plain,(
    ! [B_167] :
      ( ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ v1_compts_1('#skF_10')
      | ~ l1_pre_topc('#skF_10')
      | ~ v2_pre_topc('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_72,c_3196])).

tff(c_3203,plain,(
    ! [B_167] :
      ( ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_167))
      | ~ l1_waybel_0(B_167,'#skF_10')
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_3200])).

tff(c_3205,plain,(
    ! [B_806] :
      ( ~ r3_waybel_9('#skF_10','#skF_11','#skF_6'('#skF_10',B_806))
      | ~ l1_waybel_0(B_806,'#skF_10')
      | ~ v7_waybel_0(B_806)
      | ~ v4_orders_2(B_806)
      | v2_struct_0(B_806) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3203])).

tff(c_3209,plain,
    ( ~ l1_waybel_0('#skF_11','#skF_10')
    | ~ v7_waybel_0('#skF_11')
    | ~ v4_orders_2('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ v1_compts_1('#skF_10')
    | ~ l1_pre_topc('#skF_10')
    | ~ v2_pre_topc('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_3205])).

tff(c_3212,plain,
    ( v2_struct_0('#skF_11')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_2818,c_2822,c_2827,c_2829,c_3209])).

tff(c_3214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2817,c_3212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.49/2.68  
% 8.49/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.49/2.69  %$ r3_waybel_9 > r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_12 > #skF_1
% 8.49/2.69  
% 8.49/2.69  %Foreground sorts:
% 8.49/2.69  
% 8.49/2.69  
% 8.49/2.69  %Background operators:
% 8.49/2.69  
% 8.49/2.69  
% 8.49/2.69  %Foreground operators:
% 8.49/2.69  tff('#skF_9', type, '#skF_9': $i > $i).
% 8.49/2.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.49/2.69  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.49/2.69  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 8.49/2.69  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 8.49/2.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.49/2.69  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 8.49/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.49/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.49/2.69  tff('#skF_11', type, '#skF_11': $i).
% 8.49/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.49/2.69  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 8.49/2.69  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 8.49/2.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.49/2.69  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 8.49/2.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.49/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.49/2.69  tff('#skF_10', type, '#skF_10': $i).
% 8.49/2.69  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 8.49/2.69  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 8.49/2.69  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.49/2.69  tff(k6_yellow_6, type, k6_yellow_6: $i > $i).
% 8.49/2.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.49/2.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.49/2.69  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.49/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.49/2.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.49/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.49/2.69  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 8.49/2.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.49/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.49/2.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.49/2.69  tff('#skF_12', type, '#skF_12': $i > $i).
% 8.49/2.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 8.49/2.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.49/2.69  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 8.49/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.49/2.69  
% 8.69/2.75  tff(f_318, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 8.69/2.75  tff(f_265, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 8.69/2.75  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.69/2.75  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.69/2.75  tff(f_76, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 8.69/2.75  tff(f_94, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 8.69/2.75  tff(f_212, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 8.69/2.75  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.69/2.75  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.69/2.75  tff(f_120, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 8.69/2.75  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> (![D]: (m1_connsp_2(D, A, C) => r2_waybel_0(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_waybel_9)).
% 8.69/2.75  tff(f_143, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 8.69/2.75  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 8.69/2.75  tff(f_241, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 8.69/2.75  tff(c_94, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_104, plain, (~v2_struct_0('#skF_11') | ~v1_compts_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_132, plain, (~v1_compts_1('#skF_10')), inference(splitLeft, [status(thm)], [c_104])).
% 8.69/2.75  tff(c_92, plain, (v2_pre_topc('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_90, plain, (l1_pre_topc('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_66, plain, (![A_160]: (v4_orders_2('#skF_7'(A_160)) | v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_64, plain, (![A_160]: (v7_waybel_0('#skF_7'(A_160)) | v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_62, plain, (![A_160]: (l1_waybel_0('#skF_7'(A_160), A_160) | v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.69/2.75  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.69/2.75  tff(c_12, plain, (![A_9, B_53, C_75]: (m1_subset_1('#skF_2'(A_9, B_53, C_75), u1_struct_0(A_9)) | k10_yellow_6(A_9, B_53)=C_75 | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.69/2.75  tff(c_32, plain, (![A_93, B_94]: (m1_subset_1(k10_yellow_6(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.69/2.75  tff(c_364, plain, (![A_314, B_315, D_316]: (m1_connsp_2('#skF_1'(A_314, B_315, k10_yellow_6(A_314, B_315), D_316), A_314, D_316) | r2_hidden(D_316, k10_yellow_6(A_314, B_315)) | ~m1_subset_1(D_316, u1_struct_0(A_314)) | ~m1_subset_1(k10_yellow_6(A_314, B_315), k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_waybel_0(B_315, A_314) | ~v7_waybel_0(B_315) | ~v4_orders_2(B_315) | v2_struct_0(B_315) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.69/2.75  tff(c_367, plain, (![A_93, B_94, D_316]: (m1_connsp_2('#skF_1'(A_93, B_94, k10_yellow_6(A_93, B_94), D_316), A_93, D_316) | r2_hidden(D_316, k10_yellow_6(A_93, B_94)) | ~m1_subset_1(D_316, u1_struct_0(A_93)) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_32, c_364])).
% 8.69/2.75  tff(c_375, plain, (![A_320, B_321, C_322, E_323]: (r2_hidden('#skF_2'(A_320, B_321, C_322), C_322) | r1_waybel_0(A_320, B_321, E_323) | ~m1_connsp_2(E_323, A_320, '#skF_2'(A_320, B_321, C_322)) | k10_yellow_6(A_320, B_321)=C_322 | ~m1_subset_1(C_322, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_waybel_0(B_321, A_320) | ~v7_waybel_0(B_321) | ~v4_orders_2(B_321) | v2_struct_0(B_321) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | v2_struct_0(A_320))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.69/2.75  tff(c_593, plain, (![A_457, B_458, C_459, B_460]: (r2_hidden('#skF_2'(A_457, B_458, C_459), C_459) | r1_waybel_0(A_457, B_458, '#skF_1'(A_457, B_460, k10_yellow_6(A_457, B_460), '#skF_2'(A_457, B_458, C_459))) | k10_yellow_6(A_457, B_458)=C_459 | ~m1_subset_1(C_459, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_waybel_0(B_458, A_457) | ~v7_waybel_0(B_458) | ~v4_orders_2(B_458) | v2_struct_0(B_458) | r2_hidden('#skF_2'(A_457, B_458, C_459), k10_yellow_6(A_457, B_460)) | ~m1_subset_1('#skF_2'(A_457, B_458, C_459), u1_struct_0(A_457)) | ~l1_waybel_0(B_460, A_457) | ~v7_waybel_0(B_460) | ~v4_orders_2(B_460) | v2_struct_0(B_460) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(resolution, [status(thm)], [c_367, c_375])).
% 8.69/2.75  tff(c_28, plain, (![A_9, B_53, D_86]: (~r1_waybel_0(A_9, B_53, '#skF_1'(A_9, B_53, k10_yellow_6(A_9, B_53), D_86)) | r2_hidden(D_86, k10_yellow_6(A_9, B_53)) | ~m1_subset_1(D_86, u1_struct_0(A_9)) | ~m1_subset_1(k10_yellow_6(A_9, B_53), k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.69/2.75  tff(c_613, plain, (![A_461, B_462, C_463]: (~m1_subset_1(k10_yellow_6(A_461, B_462), k1_zfmisc_1(u1_struct_0(A_461))) | r2_hidden('#skF_2'(A_461, B_462, C_463), C_463) | k10_yellow_6(A_461, B_462)=C_463 | ~m1_subset_1(C_463, k1_zfmisc_1(u1_struct_0(A_461))) | r2_hidden('#skF_2'(A_461, B_462, C_463), k10_yellow_6(A_461, B_462)) | ~m1_subset_1('#skF_2'(A_461, B_462, C_463), u1_struct_0(A_461)) | ~l1_waybel_0(B_462, A_461) | ~v7_waybel_0(B_462) | ~v4_orders_2(B_462) | v2_struct_0(B_462) | ~l1_pre_topc(A_461) | ~v2_pre_topc(A_461) | v2_struct_0(A_461))), inference(resolution, [status(thm)], [c_593, c_28])).
% 8.69/2.75  tff(c_633, plain, (![A_464, B_465, C_466]: (r2_hidden('#skF_2'(A_464, B_465, C_466), C_466) | k10_yellow_6(A_464, B_465)=C_466 | ~m1_subset_1(C_466, k1_zfmisc_1(u1_struct_0(A_464))) | r2_hidden('#skF_2'(A_464, B_465, C_466), k10_yellow_6(A_464, B_465)) | ~m1_subset_1('#skF_2'(A_464, B_465, C_466), u1_struct_0(A_464)) | ~l1_waybel_0(B_465, A_464) | ~v7_waybel_0(B_465) | ~v4_orders_2(B_465) | v2_struct_0(B_465) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464) | v2_struct_0(A_464))), inference(resolution, [status(thm)], [c_32, c_613])).
% 8.69/2.75  tff(c_54, plain, (![A_139, B_143, C_145]: (r3_waybel_9(A_139, B_143, C_145) | ~r2_hidden(C_145, k10_yellow_6(A_139, B_143)) | ~m1_subset_1(C_145, u1_struct_0(A_139)) | ~l1_waybel_0(B_143, A_139) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.69/2.75  tff(c_681, plain, (![A_471, B_472, C_473]: (r3_waybel_9(A_471, B_472, '#skF_2'(A_471, B_472, C_473)) | r2_hidden('#skF_2'(A_471, B_472, C_473), C_473) | k10_yellow_6(A_471, B_472)=C_473 | ~m1_subset_1(C_473, k1_zfmisc_1(u1_struct_0(A_471))) | ~m1_subset_1('#skF_2'(A_471, B_472, C_473), u1_struct_0(A_471)) | ~l1_waybel_0(B_472, A_471) | ~v7_waybel_0(B_472) | ~v4_orders_2(B_472) | v2_struct_0(B_472) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(resolution, [status(thm)], [c_633, c_54])).
% 8.69/2.75  tff(c_685, plain, (![A_474, B_475, C_476]: (r3_waybel_9(A_474, B_475, '#skF_2'(A_474, B_475, C_476)) | r2_hidden('#skF_2'(A_474, B_475, C_476), C_476) | k10_yellow_6(A_474, B_475)=C_476 | ~m1_subset_1(C_476, k1_zfmisc_1(u1_struct_0(A_474))) | ~l1_waybel_0(B_475, A_474) | ~v7_waybel_0(B_475) | ~v4_orders_2(B_475) | v2_struct_0(B_475) | ~l1_pre_topc(A_474) | ~v2_pre_topc(A_474) | v2_struct_0(A_474))), inference(resolution, [status(thm)], [c_12, c_681])).
% 8.69/2.75  tff(c_693, plain, (![A_477, B_478]: (r3_waybel_9(A_477, B_478, '#skF_2'(A_477, B_478, k1_xboole_0)) | r2_hidden('#skF_2'(A_477, B_478, k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_477, B_478)=k1_xboole_0 | ~l1_waybel_0(B_478, A_477) | ~v7_waybel_0(B_478) | ~v4_orders_2(B_478) | v2_struct_0(B_478) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477))), inference(resolution, [status(thm)], [c_4, c_685])).
% 8.69/2.75  tff(c_60, plain, (![A_160, C_170]: (~r3_waybel_9(A_160, '#skF_7'(A_160), C_170) | ~m1_subset_1(C_170, u1_struct_0(A_160)) | v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_749, plain, (![A_481]: (~m1_subset_1('#skF_2'(A_481, '#skF_7'(A_481), k1_xboole_0), u1_struct_0(A_481)) | v1_compts_1(A_481) | r2_hidden('#skF_2'(A_481, '#skF_7'(A_481), k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_481, '#skF_7'(A_481))=k1_xboole_0 | ~l1_waybel_0('#skF_7'(A_481), A_481) | ~v7_waybel_0('#skF_7'(A_481)) | ~v4_orders_2('#skF_7'(A_481)) | v2_struct_0('#skF_7'(A_481)) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_693, c_60])).
% 8.69/2.75  tff(c_753, plain, (![A_9]: (v1_compts_1(A_9) | r2_hidden('#skF_2'(A_9, '#skF_7'(A_9), k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_9, '#skF_7'(A_9))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0('#skF_7'(A_9), A_9) | ~v7_waybel_0('#skF_7'(A_9)) | ~v4_orders_2('#skF_7'(A_9)) | v2_struct_0('#skF_7'(A_9)) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_749])).
% 8.69/2.75  tff(c_757, plain, (![A_482]: (v1_compts_1(A_482) | r2_hidden('#skF_2'(A_482, '#skF_7'(A_482), k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_482, '#skF_7'(A_482))=k1_xboole_0 | ~l1_waybel_0('#skF_7'(A_482), A_482) | ~v7_waybel_0('#skF_7'(A_482)) | ~v4_orders_2('#skF_7'(A_482)) | v2_struct_0('#skF_7'(A_482)) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_753])).
% 8.69/2.75  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.69/2.75  tff(c_762, plain, (![A_482]: (~r1_tarski(k1_xboole_0, '#skF_2'(A_482, '#skF_7'(A_482), k1_xboole_0)) | v1_compts_1(A_482) | k10_yellow_6(A_482, '#skF_7'(A_482))=k1_xboole_0 | ~l1_waybel_0('#skF_7'(A_482), A_482) | ~v7_waybel_0('#skF_7'(A_482)) | ~v4_orders_2('#skF_7'(A_482)) | v2_struct_0('#skF_7'(A_482)) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_757, c_8])).
% 8.69/2.75  tff(c_767, plain, (![A_483]: (v1_compts_1(A_483) | k10_yellow_6(A_483, '#skF_7'(A_483))=k1_xboole_0 | ~l1_waybel_0('#skF_7'(A_483), A_483) | ~v7_waybel_0('#skF_7'(A_483)) | ~v4_orders_2('#skF_7'(A_483)) | v2_struct_0('#skF_7'(A_483)) | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_762])).
% 8.69/2.75  tff(c_772, plain, (![A_484]: (k10_yellow_6(A_484, '#skF_7'(A_484))=k1_xboole_0 | ~v7_waybel_0('#skF_7'(A_484)) | ~v4_orders_2('#skF_7'(A_484)) | v2_struct_0('#skF_7'(A_484)) | v1_compts_1(A_484) | ~l1_pre_topc(A_484) | ~v2_pre_topc(A_484) | v2_struct_0(A_484))), inference(resolution, [status(thm)], [c_62, c_767])).
% 8.69/2.75  tff(c_776, plain, (![A_485]: (k10_yellow_6(A_485, '#skF_7'(A_485))=k1_xboole_0 | ~v4_orders_2('#skF_7'(A_485)) | v2_struct_0('#skF_7'(A_485)) | v1_compts_1(A_485) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(resolution, [status(thm)], [c_64, c_772])).
% 8.69/2.75  tff(c_797, plain, (![A_490]: (k10_yellow_6(A_490, '#skF_7'(A_490))=k1_xboole_0 | v2_struct_0('#skF_7'(A_490)) | v1_compts_1(A_490) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_66, c_776])).
% 8.69/2.75  tff(c_68, plain, (![A_160]: (~v2_struct_0('#skF_7'(A_160)) | v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_853, plain, (![A_491]: (k10_yellow_6(A_491, '#skF_7'(A_491))=k1_xboole_0 | v1_compts_1(A_491) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(resolution, [status(thm)], [c_797, c_68])).
% 8.69/2.75  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.69/2.75  tff(c_130, plain, (![B_190]: (v1_compts_1('#skF_10') | m2_yellow_6('#skF_12'(B_190), '#skF_10', B_190) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_159, plain, (![B_190]: (m2_yellow_6('#skF_12'(B_190), '#skF_10', B_190) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_132, c_130])).
% 8.69/2.75  tff(c_163, plain, (![C_218, A_219, B_220]: (~v2_struct_0(C_218) | ~m2_yellow_6(C_218, A_219, B_220) | ~l1_waybel_0(B_220, A_219) | ~v7_waybel_0(B_220) | ~v4_orders_2(B_220) | v2_struct_0(B_220) | ~l1_struct_0(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_166, plain, (![B_190]: (~v2_struct_0('#skF_12'(B_190)) | ~l1_struct_0('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_159, c_163])).
% 8.69/2.75  tff(c_169, plain, (![B_190]: (~v2_struct_0('#skF_12'(B_190)) | ~l1_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_166])).
% 8.69/2.75  tff(c_170, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_169])).
% 8.69/2.75  tff(c_173, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_10, c_170])).
% 8.69/2.75  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_173])).
% 8.69/2.75  tff(c_179, plain, (l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_169])).
% 8.69/2.75  tff(c_368, plain, (![A_317, B_318, D_319]: (m1_connsp_2('#skF_1'(A_317, B_318, k10_yellow_6(A_317, B_318), D_319), A_317, D_319) | r2_hidden(D_319, k10_yellow_6(A_317, B_318)) | ~m1_subset_1(D_319, u1_struct_0(A_317)) | ~l1_waybel_0(B_318, A_317) | ~v7_waybel_0(B_318) | ~v4_orders_2(B_318) | v2_struct_0(B_318) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_32, c_364])).
% 8.69/2.75  tff(c_48, plain, (![A_117, B_129, D_138, C_135]: (r2_waybel_0(A_117, B_129, D_138) | ~m1_connsp_2(D_138, A_117, C_135) | ~r3_waybel_9(A_117, B_129, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_117)) | ~l1_waybel_0(B_129, A_117) | v2_struct_0(B_129) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.69/2.75  tff(c_403, plain, (![A_341, B_342, B_343, D_344]: (r2_waybel_0(A_341, B_342, '#skF_1'(A_341, B_343, k10_yellow_6(A_341, B_343), D_344)) | ~r3_waybel_9(A_341, B_342, D_344) | ~l1_waybel_0(B_342, A_341) | v2_struct_0(B_342) | r2_hidden(D_344, k10_yellow_6(A_341, B_343)) | ~m1_subset_1(D_344, u1_struct_0(A_341)) | ~l1_waybel_0(B_343, A_341) | ~v7_waybel_0(B_343) | ~v4_orders_2(B_343) | v2_struct_0(B_343) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(resolution, [status(thm)], [c_368, c_48])).
% 8.69/2.75  tff(c_42, plain, (![A_99, B_107, D_113, C_111]: (r2_waybel_0(A_99, B_107, D_113) | ~r2_waybel_0(A_99, C_111, D_113) | ~m2_yellow_6(C_111, A_99, B_107) | ~l1_waybel_0(B_107, A_99) | ~v7_waybel_0(B_107) | ~v4_orders_2(B_107) | v2_struct_0(B_107) | ~l1_struct_0(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.69/2.75  tff(c_482, plain, (![D_409, B_410, A_408, B_407, B_406]: (r2_waybel_0(A_408, B_410, '#skF_1'(A_408, B_407, k10_yellow_6(A_408, B_407), D_409)) | ~m2_yellow_6(B_406, A_408, B_410) | ~l1_waybel_0(B_410, A_408) | ~v7_waybel_0(B_410) | ~v4_orders_2(B_410) | v2_struct_0(B_410) | ~l1_struct_0(A_408) | ~r3_waybel_9(A_408, B_406, D_409) | ~l1_waybel_0(B_406, A_408) | v2_struct_0(B_406) | r2_hidden(D_409, k10_yellow_6(A_408, B_407)) | ~m1_subset_1(D_409, u1_struct_0(A_408)) | ~l1_waybel_0(B_407, A_408) | ~v7_waybel_0(B_407) | ~v4_orders_2(B_407) | v2_struct_0(B_407) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_403, c_42])).
% 8.69/2.75  tff(c_486, plain, (![B_190, B_407, D_409]: (r2_waybel_0('#skF_10', B_190, '#skF_1'('#skF_10', B_407, k10_yellow_6('#skF_10', B_407), D_409)) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), D_409) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r2_hidden(D_409, k10_yellow_6('#skF_10', B_407)) | ~m1_subset_1(D_409, u1_struct_0('#skF_10')) | ~l1_waybel_0(B_407, '#skF_10') | ~v7_waybel_0(B_407) | ~v4_orders_2(B_407) | v2_struct_0(B_407) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_159, c_482])).
% 8.69/2.75  tff(c_490, plain, (![B_190, B_407, D_409]: (r2_waybel_0('#skF_10', B_190, '#skF_1'('#skF_10', B_407, k10_yellow_6('#skF_10', B_407), D_409)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), D_409) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r2_hidden(D_409, k10_yellow_6('#skF_10', B_407)) | ~m1_subset_1(D_409, u1_struct_0('#skF_10')) | ~l1_waybel_0(B_407, '#skF_10') | ~v7_waybel_0(B_407) | ~v4_orders_2(B_407) | v2_struct_0(B_407) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_179, c_486])).
% 8.69/2.75  tff(c_491, plain, (![B_190, B_407, D_409]: (r2_waybel_0('#skF_10', B_190, '#skF_1'('#skF_10', B_407, k10_yellow_6('#skF_10', B_407), D_409)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), D_409) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r2_hidden(D_409, k10_yellow_6('#skF_10', B_407)) | ~m1_subset_1(D_409, u1_struct_0('#skF_10')) | ~l1_waybel_0(B_407, '#skF_10') | ~v7_waybel_0(B_407) | ~v4_orders_2(B_407) | v2_struct_0(B_407) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_490])).
% 8.69/2.75  tff(c_880, plain, (![B_190, D_409]: (r2_waybel_0('#skF_10', B_190, '#skF_1'('#skF_10', '#skF_7'('#skF_10'), k1_xboole_0, D_409)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), D_409) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r2_hidden(D_409, k10_yellow_6('#skF_10', '#skF_7'('#skF_10'))) | ~m1_subset_1(D_409, u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_853, c_491])).
% 8.69/2.75  tff(c_906, plain, (![B_190, D_409]: (r2_waybel_0('#skF_10', B_190, '#skF_1'('#skF_10', '#skF_7'('#skF_10'), k1_xboole_0, D_409)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), D_409) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r2_hidden(D_409, k10_yellow_6('#skF_10', '#skF_7'('#skF_10'))) | ~m1_subset_1(D_409, u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | v1_compts_1('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_880])).
% 8.69/2.75  tff(c_907, plain, (![B_190, D_409]: (r2_waybel_0('#skF_10', B_190, '#skF_1'('#skF_10', '#skF_7'('#skF_10'), k1_xboole_0, D_409)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), D_409) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r2_hidden(D_409, k10_yellow_6('#skF_10', '#skF_7'('#skF_10'))) | ~m1_subset_1(D_409, u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_906])).
% 8.69/2.75  tff(c_1578, plain, (~v4_orders_2('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_907])).
% 8.69/2.75  tff(c_1581, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_66, c_1578])).
% 8.69/2.75  tff(c_1584, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1581])).
% 8.69/2.75  tff(c_1586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1584])).
% 8.69/2.75  tff(c_1588, plain, (v4_orders_2('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_907])).
% 8.69/2.75  tff(c_199, plain, (![C_230, A_231, B_232]: (l1_waybel_0(C_230, A_231) | ~m2_yellow_6(C_230, A_231, B_232) | ~l1_waybel_0(B_232, A_231) | ~v7_waybel_0(B_232) | ~v4_orders_2(B_232) | v2_struct_0(B_232) | ~l1_struct_0(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_202, plain, (![B_190]: (l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~l1_struct_0('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_159, c_199])).
% 8.69/2.75  tff(c_205, plain, (![B_190]: (l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_202])).
% 8.69/2.75  tff(c_206, plain, (![B_190]: (l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_205])).
% 8.69/2.75  tff(c_181, plain, (![C_222, A_223, B_224]: (v4_orders_2(C_222) | ~m2_yellow_6(C_222, A_223, B_224) | ~l1_waybel_0(B_224, A_223) | ~v7_waybel_0(B_224) | ~v4_orders_2(B_224) | v2_struct_0(B_224) | ~l1_struct_0(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_184, plain, (![B_190]: (v4_orders_2('#skF_12'(B_190)) | ~l1_struct_0('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_159, c_181])).
% 8.69/2.75  tff(c_187, plain, (![B_190]: (v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_184])).
% 8.69/2.75  tff(c_188, plain, (![B_190]: (v4_orders_2('#skF_12'(B_190)) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_187])).
% 8.69/2.75  tff(c_52, plain, (![A_117, B_129, C_135]: (m1_connsp_2('#skF_4'(A_117, B_129, C_135), A_117, C_135) | r3_waybel_9(A_117, B_129, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_117)) | ~l1_waybel_0(B_129, A_117) | v2_struct_0(B_129) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.69/2.75  tff(c_262, plain, (![A_262, B_263, D_264, C_265]: (r2_waybel_0(A_262, B_263, D_264) | ~m1_connsp_2(D_264, A_262, C_265) | ~r3_waybel_9(A_262, B_263, C_265) | ~m1_subset_1(C_265, u1_struct_0(A_262)) | ~l1_waybel_0(B_263, A_262) | v2_struct_0(B_263) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.69/2.75  tff(c_342, plain, (![A_297, B_298, B_299, C_300]: (r2_waybel_0(A_297, B_298, '#skF_4'(A_297, B_299, C_300)) | ~r3_waybel_9(A_297, B_298, C_300) | ~l1_waybel_0(B_298, A_297) | v2_struct_0(B_298) | r3_waybel_9(A_297, B_299, C_300) | ~m1_subset_1(C_300, u1_struct_0(A_297)) | ~l1_waybel_0(B_299, A_297) | v2_struct_0(B_299) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297))), inference(resolution, [status(thm)], [c_52, c_262])).
% 8.69/2.75  tff(c_424, plain, (![B_372, B_370, A_371, C_369, B_373]: (r2_waybel_0(A_371, B_373, '#skF_4'(A_371, B_370, C_369)) | ~m2_yellow_6(B_372, A_371, B_373) | ~l1_waybel_0(B_373, A_371) | ~v7_waybel_0(B_373) | ~v4_orders_2(B_373) | v2_struct_0(B_373) | ~l1_struct_0(A_371) | ~r3_waybel_9(A_371, B_372, C_369) | ~l1_waybel_0(B_372, A_371) | v2_struct_0(B_372) | r3_waybel_9(A_371, B_370, C_369) | ~m1_subset_1(C_369, u1_struct_0(A_371)) | ~l1_waybel_0(B_370, A_371) | v2_struct_0(B_370) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(resolution, [status(thm)], [c_342, c_42])).
% 8.69/2.75  tff(c_428, plain, (![B_190, B_370, C_369]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, C_369)) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), C_369) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r3_waybel_9('#skF_10', B_370, C_369) | ~m1_subset_1(C_369, u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_159, c_424])).
% 8.69/2.75  tff(c_432, plain, (![B_190, B_370, C_369]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, C_369)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), C_369) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r3_waybel_9('#skF_10', B_370, C_369) | ~m1_subset_1(C_369, u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_179, c_428])).
% 8.69/2.75  tff(c_433, plain, (![B_190, B_370, C_369]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, C_369)) | ~r3_waybel_9('#skF_10', '#skF_12'(B_190), C_369) | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | v2_struct_0('#skF_12'(B_190)) | r3_waybel_9('#skF_10', B_370, C_369) | ~m1_subset_1(C_369, u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_432])).
% 8.69/2.75  tff(c_707, plain, (![B_190, B_370]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0))) | r3_waybel_9('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_190))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~v7_waybel_0('#skF_12'(B_190)) | ~v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_12'(B_190)) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_693, c_433])).
% 8.69/2.75  tff(c_730, plain, (![B_190, B_370]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0))) | r3_waybel_9('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_190))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~v7_waybel_0('#skF_12'(B_190)) | ~v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_12'(B_190)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_707])).
% 8.69/2.75  tff(c_734, plain, (![B_479, B_480]: (r2_waybel_0('#skF_10', B_479, '#skF_4'('#skF_10', B_480, '#skF_2'('#skF_10', '#skF_12'(B_479), k1_xboole_0))) | r3_waybel_9('#skF_10', B_480, '#skF_2'('#skF_10', '#skF_12'(B_479), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_479), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_480, '#skF_10') | v2_struct_0(B_480) | ~l1_waybel_0(B_479, '#skF_10') | ~v7_waybel_0(B_479) | ~v4_orders_2(B_479) | v2_struct_0(B_479) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_479), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_479))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_479), '#skF_10') | ~v7_waybel_0('#skF_12'(B_479)) | ~v4_orders_2('#skF_12'(B_479)) | v2_struct_0('#skF_12'(B_479)))), inference(negUnitSimplification, [status(thm)], [c_94, c_730])).
% 8.69/2.75  tff(c_50, plain, (![A_117, B_129, C_135]: (~r2_waybel_0(A_117, B_129, '#skF_4'(A_117, B_129, C_135)) | r3_waybel_9(A_117, B_129, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_117)) | ~l1_waybel_0(B_129, A_117) | v2_struct_0(B_129) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.69/2.75  tff(c_738, plain, (![B_480]: (~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | r3_waybel_9('#skF_10', B_480, '#skF_2'('#skF_10', '#skF_12'(B_480), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_480), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_480, '#skF_10') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_480), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_480))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_480), '#skF_10') | ~v7_waybel_0('#skF_12'(B_480)) | ~v4_orders_2('#skF_12'(B_480)) | v2_struct_0('#skF_12'(B_480)))), inference(resolution, [status(thm)], [c_734, c_50])).
% 8.69/2.75  tff(c_743, plain, (![B_480]: (v2_struct_0('#skF_10') | r3_waybel_9('#skF_10', B_480, '#skF_2'('#skF_10', '#skF_12'(B_480), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_480), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_480, '#skF_10') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_480), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_480))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_480), '#skF_10') | ~v7_waybel_0('#skF_12'(B_480)) | ~v4_orders_2('#skF_12'(B_480)) | v2_struct_0('#skF_12'(B_480)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_738])).
% 8.69/2.75  tff(c_910, plain, (![B_492]: (r3_waybel_9('#skF_10', B_492, '#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_492, '#skF_10') | ~v7_waybel_0(B_492) | ~v4_orders_2(B_492) | v2_struct_0(B_492) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_492))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_492), '#skF_10') | ~v7_waybel_0('#skF_12'(B_492)) | ~v4_orders_2('#skF_12'(B_492)) | v2_struct_0('#skF_12'(B_492)))), inference(negUnitSimplification, [status(thm)], [c_94, c_743])).
% 8.69/2.75  tff(c_913, plain, (![B_492]: (r3_waybel_9('#skF_10', B_492, '#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0)) | ~l1_waybel_0(B_492, '#skF_10') | ~v7_waybel_0(B_492) | ~v4_orders_2(B_492) | v2_struct_0(B_492) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_492))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_10'))) | ~l1_waybel_0('#skF_12'(B_492), '#skF_10') | ~v7_waybel_0('#skF_12'(B_492)) | ~v4_orders_2('#skF_12'(B_492)) | v2_struct_0('#skF_12'(B_492)) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_12, c_910])).
% 8.69/2.75  tff(c_916, plain, (![B_492]: (r3_waybel_9('#skF_10', B_492, '#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0)) | ~l1_waybel_0(B_492, '#skF_10') | ~v7_waybel_0(B_492) | ~v4_orders_2(B_492) | v2_struct_0(B_492) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_492), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_492))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_492), '#skF_10') | ~v7_waybel_0('#skF_12'(B_492)) | ~v4_orders_2('#skF_12'(B_492)) | v2_struct_0('#skF_12'(B_492)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_4, c_913])).
% 8.69/2.75  tff(c_1034, plain, (![B_508]: (r3_waybel_9('#skF_10', B_508, '#skF_2'('#skF_10', '#skF_12'(B_508), k1_xboole_0)) | ~l1_waybel_0(B_508, '#skF_10') | ~v7_waybel_0(B_508) | ~v4_orders_2(B_508) | v2_struct_0(B_508) | r2_hidden('#skF_2'('#skF_10', '#skF_12'(B_508), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'(B_508))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_508), '#skF_10') | ~v7_waybel_0('#skF_12'(B_508)) | ~v4_orders_2('#skF_12'(B_508)) | v2_struct_0('#skF_12'(B_508)))), inference(negUnitSimplification, [status(thm)], [c_94, c_916])).
% 8.69/2.75  tff(c_1054, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | r2_hidden('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | ~v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(resolution, [status(thm)], [c_1034, c_60])).
% 8.69/2.75  tff(c_1076, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | v1_compts_1('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | r2_hidden('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | ~v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1054])).
% 8.69/2.75  tff(c_1077, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | r2_hidden('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | ~v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1076])).
% 8.69/2.75  tff(c_1398, plain, (~v4_orders_2('#skF_12'('#skF_7'('#skF_10')))), inference(splitLeft, [status(thm)], [c_1077])).
% 8.69/2.75  tff(c_1402, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(resolution, [status(thm)], [c_188, c_1398])).
% 8.69/2.75  tff(c_1403, plain, (~v4_orders_2('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_1402])).
% 8.69/2.75  tff(c_1406, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_66, c_1403])).
% 8.69/2.75  tff(c_1409, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1406])).
% 8.69/2.75  tff(c_1411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1409])).
% 8.69/2.75  tff(c_1412, plain, (~v7_waybel_0('#skF_7'('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1402])).
% 8.69/2.75  tff(c_1414, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_1412])).
% 8.69/2.75  tff(c_1439, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_1414])).
% 8.69/2.75  tff(c_1442, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1439])).
% 8.69/2.75  tff(c_1444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1442])).
% 8.69/2.75  tff(c_1445, plain, (~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1412])).
% 8.69/2.75  tff(c_1447, plain, (~v7_waybel_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_1445])).
% 8.69/2.75  tff(c_1451, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_64, c_1447])).
% 8.69/2.75  tff(c_1454, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1451])).
% 8.69/2.75  tff(c_1456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1454])).
% 8.69/2.75  tff(c_1457, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1445])).
% 8.69/2.75  tff(c_1461, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_1457, c_68])).
% 8.69/2.75  tff(c_1464, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1461])).
% 8.69/2.75  tff(c_1466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1464])).
% 8.69/2.75  tff(c_1468, plain, (v4_orders_2('#skF_12'('#skF_7'('#skF_10')))), inference(splitRight, [status(thm)], [c_1077])).
% 8.69/2.75  tff(c_190, plain, (![C_226, A_227, B_228]: (v7_waybel_0(C_226) | ~m2_yellow_6(C_226, A_227, B_228) | ~l1_waybel_0(B_228, A_227) | ~v7_waybel_0(B_228) | ~v4_orders_2(B_228) | v2_struct_0(B_228) | ~l1_struct_0(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_193, plain, (![B_190]: (v7_waybel_0('#skF_12'(B_190)) | ~l1_struct_0('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_159, c_190])).
% 8.69/2.75  tff(c_196, plain, (![B_190]: (v7_waybel_0('#skF_12'(B_190)) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_193])).
% 8.69/2.75  tff(c_197, plain, (![B_190]: (v7_waybel_0('#skF_12'(B_190)) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_94, c_196])).
% 8.69/2.75  tff(c_1186, plain, (![C_519, A_520, B_521]: (~r1_tarski(C_519, '#skF_2'(A_520, B_521, C_519)) | k10_yellow_6(A_520, B_521)=C_519 | ~m1_subset_1(C_519, k1_zfmisc_1(u1_struct_0(A_520))) | r2_hidden('#skF_2'(A_520, B_521, C_519), k10_yellow_6(A_520, B_521)) | ~m1_subset_1('#skF_2'(A_520, B_521, C_519), u1_struct_0(A_520)) | ~l1_waybel_0(B_521, A_520) | ~v7_waybel_0(B_521) | ~v4_orders_2(B_521) | v2_struct_0(B_521) | ~l1_pre_topc(A_520) | ~v2_pre_topc(A_520) | v2_struct_0(A_520))), inference(resolution, [status(thm)], [c_633, c_8])).
% 8.69/2.75  tff(c_1189, plain, (![A_520, B_521]: (k10_yellow_6(A_520, B_521)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_520))) | r2_hidden('#skF_2'(A_520, B_521, k1_xboole_0), k10_yellow_6(A_520, B_521)) | ~m1_subset_1('#skF_2'(A_520, B_521, k1_xboole_0), u1_struct_0(A_520)) | ~l1_waybel_0(B_521, A_520) | ~v7_waybel_0(B_521) | ~v4_orders_2(B_521) | v2_struct_0(B_521) | ~l1_pre_topc(A_520) | ~v2_pre_topc(A_520) | v2_struct_0(A_520))), inference(resolution, [status(thm)], [c_2, c_1186])).
% 8.69/2.75  tff(c_1193, plain, (![A_522, B_523]: (k10_yellow_6(A_522, B_523)=k1_xboole_0 | r2_hidden('#skF_2'(A_522, B_523, k1_xboole_0), k10_yellow_6(A_522, B_523)) | ~m1_subset_1('#skF_2'(A_522, B_523, k1_xboole_0), u1_struct_0(A_522)) | ~l1_waybel_0(B_523, A_522) | ~v7_waybel_0(B_523) | ~v4_orders_2(B_523) | v2_struct_0(B_523) | ~l1_pre_topc(A_522) | ~v2_pre_topc(A_522) | v2_struct_0(A_522))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1189])).
% 8.69/2.75  tff(c_1299, plain, (![A_529, B_530]: (r3_waybel_9(A_529, B_530, '#skF_2'(A_529, B_530, k1_xboole_0)) | k10_yellow_6(A_529, B_530)=k1_xboole_0 | ~m1_subset_1('#skF_2'(A_529, B_530, k1_xboole_0), u1_struct_0(A_529)) | ~l1_waybel_0(B_530, A_529) | ~v7_waybel_0(B_530) | ~v4_orders_2(B_530) | v2_struct_0(B_530) | ~l1_pre_topc(A_529) | ~v2_pre_topc(A_529) | v2_struct_0(A_529))), inference(resolution, [status(thm)], [c_1193, c_54])).
% 8.69/2.75  tff(c_1302, plain, (![A_9, B_53]: (r3_waybel_9(A_9, B_53, '#skF_2'(A_9, B_53, k1_xboole_0)) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_1299])).
% 8.69/2.75  tff(c_1334, plain, (![A_536, B_537]: (r3_waybel_9(A_536, B_537, '#skF_2'(A_536, B_537, k1_xboole_0)) | k10_yellow_6(A_536, B_537)=k1_xboole_0 | ~l1_waybel_0(B_537, A_536) | ~v7_waybel_0(B_537) | ~v4_orders_2(B_537) | v2_struct_0(B_537) | ~l1_pre_topc(A_536) | ~v2_pre_topc(A_536) | v2_struct_0(A_536))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1302])).
% 8.69/2.75  tff(c_1350, plain, (![B_190, B_370]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0))) | r3_waybel_9('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | k10_yellow_6('#skF_10', '#skF_12'(B_190))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~v7_waybel_0('#skF_12'(B_190)) | ~v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_12'(B_190)) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_1334, c_433])).
% 8.69/2.75  tff(c_1376, plain, (![B_190, B_370]: (r2_waybel_0('#skF_10', B_190, '#skF_4'('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0))) | r3_waybel_9('#skF_10', B_370, '#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_190), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_370, '#skF_10') | v2_struct_0(B_370) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | k10_yellow_6('#skF_10', '#skF_12'(B_190))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~v7_waybel_0('#skF_12'(B_190)) | ~v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_12'(B_190)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1350])).
% 8.69/2.75  tff(c_1741, plain, (![B_592, B_593]: (r2_waybel_0('#skF_10', B_592, '#skF_4'('#skF_10', B_593, '#skF_2'('#skF_10', '#skF_12'(B_592), k1_xboole_0))) | r3_waybel_9('#skF_10', B_593, '#skF_2'('#skF_10', '#skF_12'(B_592), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_592), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_593, '#skF_10') | v2_struct_0(B_593) | ~l1_waybel_0(B_592, '#skF_10') | ~v7_waybel_0(B_592) | ~v4_orders_2(B_592) | v2_struct_0(B_592) | k10_yellow_6('#skF_10', '#skF_12'(B_592))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_592), '#skF_10') | ~v7_waybel_0('#skF_12'(B_592)) | ~v4_orders_2('#skF_12'(B_592)) | v2_struct_0('#skF_12'(B_592)))), inference(negUnitSimplification, [status(thm)], [c_94, c_1376])).
% 8.69/2.75  tff(c_1745, plain, (![B_593]: (~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | r3_waybel_9('#skF_10', B_593, '#skF_2'('#skF_10', '#skF_12'(B_593), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_593), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_593, '#skF_10') | ~v7_waybel_0(B_593) | ~v4_orders_2(B_593) | v2_struct_0(B_593) | k10_yellow_6('#skF_10', '#skF_12'(B_593))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_593), '#skF_10') | ~v7_waybel_0('#skF_12'(B_593)) | ~v4_orders_2('#skF_12'(B_593)) | v2_struct_0('#skF_12'(B_593)))), inference(resolution, [status(thm)], [c_1741, c_50])).
% 8.69/2.75  tff(c_1750, plain, (![B_593]: (v2_struct_0('#skF_10') | r3_waybel_9('#skF_10', B_593, '#skF_2'('#skF_10', '#skF_12'(B_593), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_593), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_593, '#skF_10') | ~v7_waybel_0(B_593) | ~v4_orders_2(B_593) | v2_struct_0(B_593) | k10_yellow_6('#skF_10', '#skF_12'(B_593))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_593), '#skF_10') | ~v7_waybel_0('#skF_12'(B_593)) | ~v4_orders_2('#skF_12'(B_593)) | v2_struct_0('#skF_12'(B_593)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1745])).
% 8.69/2.75  tff(c_1764, plain, (![B_596]: (r3_waybel_9('#skF_10', B_596, '#skF_2'('#skF_10', '#skF_12'(B_596), k1_xboole_0)) | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'(B_596), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0(B_596, '#skF_10') | ~v7_waybel_0(B_596) | ~v4_orders_2(B_596) | v2_struct_0(B_596) | k10_yellow_6('#skF_10', '#skF_12'(B_596))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_596), '#skF_10') | ~v7_waybel_0('#skF_12'(B_596)) | ~v4_orders_2('#skF_12'(B_596)) | v2_struct_0('#skF_12'(B_596)))), inference(negUnitSimplification, [status(thm)], [c_94, c_1750])).
% 8.69/2.75  tff(c_1767, plain, (![B_596]: (r3_waybel_9('#skF_10', B_596, '#skF_2'('#skF_10', '#skF_12'(B_596), k1_xboole_0)) | ~l1_waybel_0(B_596, '#skF_10') | ~v7_waybel_0(B_596) | ~v4_orders_2(B_596) | v2_struct_0(B_596) | k10_yellow_6('#skF_10', '#skF_12'(B_596))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_10'))) | ~l1_waybel_0('#skF_12'(B_596), '#skF_10') | ~v7_waybel_0('#skF_12'(B_596)) | ~v4_orders_2('#skF_12'(B_596)) | v2_struct_0('#skF_12'(B_596)) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_12, c_1764])).
% 8.69/2.75  tff(c_1770, plain, (![B_596]: (r3_waybel_9('#skF_10', B_596, '#skF_2'('#skF_10', '#skF_12'(B_596), k1_xboole_0)) | ~l1_waybel_0(B_596, '#skF_10') | ~v7_waybel_0(B_596) | ~v4_orders_2(B_596) | v2_struct_0(B_596) | k10_yellow_6('#skF_10', '#skF_12'(B_596))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_596), '#skF_10') | ~v7_waybel_0('#skF_12'(B_596)) | ~v4_orders_2('#skF_12'(B_596)) | v2_struct_0('#skF_12'(B_596)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_4, c_1767])).
% 8.69/2.75  tff(c_1772, plain, (![B_597]: (r3_waybel_9('#skF_10', B_597, '#skF_2'('#skF_10', '#skF_12'(B_597), k1_xboole_0)) | ~l1_waybel_0(B_597, '#skF_10') | ~v7_waybel_0(B_597) | ~v4_orders_2(B_597) | v2_struct_0(B_597) | k10_yellow_6('#skF_10', '#skF_12'(B_597))=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_597), '#skF_10') | ~v7_waybel_0('#skF_12'(B_597)) | ~v4_orders_2('#skF_12'(B_597)) | v2_struct_0('#skF_12'(B_597)))), inference(negUnitSimplification, [status(thm)], [c_94, c_1770])).
% 8.69/2.75  tff(c_1792, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | ~v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(resolution, [status(thm)], [c_1772, c_60])).
% 8.69/2.75  tff(c_1814, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | v1_compts_1('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_1588, c_92, c_90, c_1792])).
% 8.69/2.75  tff(c_1815, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1814])).
% 8.69/2.75  tff(c_1820, plain, (~v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))), inference(splitLeft, [status(thm)], [c_1815])).
% 8.69/2.75  tff(c_1823, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(resolution, [status(thm)], [c_197, c_1820])).
% 8.69/2.75  tff(c_1826, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1823])).
% 8.69/2.75  tff(c_1832, plain, (~v7_waybel_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_1826])).
% 8.69/2.75  tff(c_1835, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_64, c_1832])).
% 8.69/2.75  tff(c_1838, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1835])).
% 8.69/2.75  tff(c_1840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1838])).
% 8.69/2.75  tff(c_1841, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1826])).
% 8.69/2.75  tff(c_1850, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_1841])).
% 8.69/2.75  tff(c_1853, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_1850])).
% 8.69/2.75  tff(c_1856, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1853])).
% 8.69/2.75  tff(c_1858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1856])).
% 8.69/2.75  tff(c_1859, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1841])).
% 8.69/2.75  tff(c_1863, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_1859, c_68])).
% 8.69/2.75  tff(c_1866, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1863])).
% 8.69/2.75  tff(c_1868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1866])).
% 8.69/2.75  tff(c_1870, plain, (v7_waybel_0('#skF_12'('#skF_7'('#skF_10')))), inference(splitRight, [status(thm)], [c_1815])).
% 8.69/2.75  tff(c_1869, plain, (~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10')) | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1815])).
% 8.69/2.75  tff(c_1876, plain, (~m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10'))), inference(splitLeft, [status(thm)], [c_1869])).
% 8.69/2.75  tff(c_1879, plain, (k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_10'))) | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | ~v7_waybel_0('#skF_12'('#skF_7'('#skF_10'))) | ~v4_orders_2('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_12, c_1876])).
% 8.69/2.75  tff(c_1882, plain, (k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1468, c_1870, c_4, c_1879])).
% 8.69/2.75  tff(c_1883, plain, (k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_94, c_1882])).
% 8.69/2.75  tff(c_1884, plain, (~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10')), inference(splitLeft, [status(thm)], [c_1883])).
% 8.69/2.75  tff(c_1952, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(resolution, [status(thm)], [c_206, c_1884])).
% 8.69/2.75  tff(c_1955, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1952])).
% 8.69/2.75  tff(c_1956, plain, (~v7_waybel_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_1955])).
% 8.69/2.75  tff(c_1959, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_64, c_1956])).
% 8.69/2.75  tff(c_1962, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1959])).
% 8.69/2.75  tff(c_1964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1962])).
% 8.69/2.75  tff(c_1965, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1955])).
% 8.69/2.75  tff(c_1979, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_1965])).
% 8.69/2.75  tff(c_1982, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_1979])).
% 8.69/2.75  tff(c_1985, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1982])).
% 8.69/2.75  tff(c_1987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1985])).
% 8.69/2.75  tff(c_1988, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_1965])).
% 8.69/2.75  tff(c_1992, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_1988, c_68])).
% 8.69/2.75  tff(c_1995, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1992])).
% 8.69/2.75  tff(c_1997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_1995])).
% 8.69/2.75  tff(c_1998, plain, (v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1883])).
% 8.69/2.75  tff(c_2199, plain, (k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1998])).
% 8.69/2.75  tff(c_118, plain, (![B_190]: (v1_compts_1('#skF_10') | v3_yellow_6('#skF_12'(B_190), '#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_145, plain, (![B_190]: (v3_yellow_6('#skF_12'(B_190), '#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_132, c_118])).
% 8.69/2.75  tff(c_208, plain, (![A_234, B_235]: (k10_yellow_6(A_234, B_235)!=k1_xboole_0 | ~v3_yellow_6(B_235, A_234) | ~l1_waybel_0(B_235, A_234) | ~v7_waybel_0(B_235) | ~v4_orders_2(B_235) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.69/2.75  tff(c_211, plain, (![B_190]: (k10_yellow_6('#skF_10', '#skF_12'(B_190))!=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~v7_waybel_0('#skF_12'(B_190)) | ~v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_12'(B_190)) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(resolution, [status(thm)], [c_145, c_208])).
% 8.69/2.75  tff(c_214, plain, (![B_190]: (k10_yellow_6('#skF_10', '#skF_12'(B_190))!=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_190), '#skF_10') | ~v7_waybel_0('#skF_12'(B_190)) | ~v4_orders_2('#skF_12'(B_190)) | v2_struct_0('#skF_12'(B_190)) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_211])).
% 8.69/2.75  tff(c_239, plain, (![B_251]: (k10_yellow_6('#skF_10', '#skF_12'(B_251))!=k1_xboole_0 | ~l1_waybel_0('#skF_12'(B_251), '#skF_10') | ~v7_waybel_0('#skF_12'(B_251)) | ~v4_orders_2('#skF_12'(B_251)) | v2_struct_0('#skF_12'(B_251)) | ~l1_waybel_0(B_251, '#skF_10') | ~v7_waybel_0(B_251) | ~v4_orders_2(B_251) | v2_struct_0(B_251))), inference(negUnitSimplification, [status(thm)], [c_94, c_214])).
% 8.69/2.75  tff(c_244, plain, (![B_252]: (k10_yellow_6('#skF_10', '#skF_12'(B_252))!=k1_xboole_0 | ~v7_waybel_0('#skF_12'(B_252)) | ~v4_orders_2('#skF_12'(B_252)) | v2_struct_0('#skF_12'(B_252)) | ~l1_waybel_0(B_252, '#skF_10') | ~v7_waybel_0(B_252) | ~v4_orders_2(B_252) | v2_struct_0(B_252))), inference(resolution, [status(thm)], [c_206, c_239])).
% 8.69/2.75  tff(c_249, plain, (![B_253]: (k10_yellow_6('#skF_10', '#skF_12'(B_253))!=k1_xboole_0 | ~v4_orders_2('#skF_12'(B_253)) | v2_struct_0('#skF_12'(B_253)) | ~l1_waybel_0(B_253, '#skF_10') | ~v7_waybel_0(B_253) | ~v4_orders_2(B_253) | v2_struct_0(B_253))), inference(resolution, [status(thm)], [c_197, c_244])).
% 8.69/2.75  tff(c_254, plain, (![B_254]: (k10_yellow_6('#skF_10', '#skF_12'(B_254))!=k1_xboole_0 | v2_struct_0('#skF_12'(B_254)) | ~l1_waybel_0(B_254, '#skF_10') | ~v7_waybel_0(B_254) | ~v4_orders_2(B_254) | v2_struct_0(B_254))), inference(resolution, [status(thm)], [c_188, c_249])).
% 8.69/2.75  tff(c_178, plain, (![B_190]: (~v2_struct_0('#skF_12'(B_190)) | ~l1_waybel_0(B_190, '#skF_10') | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190))), inference(splitRight, [status(thm)], [c_169])).
% 8.69/2.75  tff(c_258, plain, (![B_254]: (k10_yellow_6('#skF_10', '#skF_12'(B_254))!=k1_xboole_0 | ~l1_waybel_0(B_254, '#skF_10') | ~v7_waybel_0(B_254) | ~v4_orders_2(B_254) | v2_struct_0(B_254))), inference(resolution, [status(thm)], [c_254, c_178])).
% 8.69/2.75  tff(c_2274, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2199, c_258])).
% 8.69/2.75  tff(c_2350, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_2274])).
% 8.69/2.75  tff(c_2358, plain, (~v7_waybel_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_2350])).
% 8.69/2.75  tff(c_2361, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_64, c_2358])).
% 8.69/2.75  tff(c_2364, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2361])).
% 8.69/2.75  tff(c_2366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2364])).
% 8.69/2.75  tff(c_2367, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2350])).
% 8.69/2.75  tff(c_2376, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_2367])).
% 8.69/2.75  tff(c_2379, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_2376])).
% 8.69/2.75  tff(c_2382, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2379])).
% 8.69/2.75  tff(c_2384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2382])).
% 8.69/2.75  tff(c_2385, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2367])).
% 8.69/2.75  tff(c_2389, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2385, c_68])).
% 8.69/2.75  tff(c_2392, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2389])).
% 8.69/2.75  tff(c_2394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2392])).
% 8.69/2.75  tff(c_2395, plain, (v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(splitRight, [status(thm)], [c_1998])).
% 8.69/2.75  tff(c_2411, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(resolution, [status(thm)], [c_2395, c_178])).
% 8.69/2.75  tff(c_2414, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_2411])).
% 8.69/2.75  tff(c_2415, plain, (~v7_waybel_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_2414])).
% 8.69/2.75  tff(c_2426, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_64, c_2415])).
% 8.69/2.75  tff(c_2429, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2426])).
% 8.69/2.75  tff(c_2431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2429])).
% 8.69/2.75  tff(c_2432, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2414])).
% 8.69/2.75  tff(c_2434, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_2432])).
% 8.69/2.75  tff(c_2437, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_2434])).
% 8.69/2.75  tff(c_2440, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2437])).
% 8.69/2.75  tff(c_2442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2440])).
% 8.69/2.75  tff(c_2443, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2432])).
% 8.69/2.75  tff(c_2447, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2443, c_68])).
% 8.69/2.75  tff(c_2450, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2447])).
% 8.69/2.75  tff(c_2452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2450])).
% 8.69/2.75  tff(c_2454, plain, (m1_subset_1('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), u1_struct_0('#skF_10'))), inference(splitRight, [status(thm)], [c_1869])).
% 8.69/2.75  tff(c_918, plain, (![A_493, C_494]: (r3_waybel_9(A_493, '#skF_7'(A_493), C_494) | ~r2_hidden(C_494, k1_xboole_0) | ~m1_subset_1(C_494, u1_struct_0(A_493)) | ~l1_waybel_0('#skF_7'(A_493), A_493) | ~v7_waybel_0('#skF_7'(A_493)) | ~v4_orders_2('#skF_7'(A_493)) | v2_struct_0('#skF_7'(A_493)) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493) | v1_compts_1(A_493) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(superposition, [status(thm), theory('equality')], [c_853, c_54])).
% 8.69/2.75  tff(c_926, plain, (![C_494, A_493]: (~r2_hidden(C_494, k1_xboole_0) | ~m1_subset_1(C_494, u1_struct_0(A_493)) | ~l1_waybel_0('#skF_7'(A_493), A_493) | ~v7_waybel_0('#skF_7'(A_493)) | ~v4_orders_2('#skF_7'(A_493)) | v2_struct_0('#skF_7'(A_493)) | v1_compts_1(A_493) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(resolution, [status(thm)], [c_918, c_60])).
% 8.69/2.75  tff(c_2470, plain, (~r2_hidden('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), k1_xboole_0) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2454, c_926])).
% 8.69/2.75  tff(c_2483, plain, (~r2_hidden('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), k1_xboole_0) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10')) | v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1588, c_2470])).
% 8.69/2.75  tff(c_2484, plain, (~r2_hidden('#skF_2'('#skF_10', '#skF_12'('#skF_7'('#skF_10')), k1_xboole_0), k1_xboole_0) | ~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2483])).
% 8.69/2.75  tff(c_2508, plain, (~v7_waybel_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_2484])).
% 8.69/2.75  tff(c_2511, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_64, c_2508])).
% 8.69/2.75  tff(c_2514, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2511])).
% 8.69/2.75  tff(c_2516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2514])).
% 8.69/2.75  tff(c_2518, plain, (v7_waybel_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2484])).
% 8.69/2.75  tff(c_2453, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | v2_struct_0('#skF_7'('#skF_10')) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(splitRight, [status(thm)], [c_1869])).
% 8.69/2.75  tff(c_2531, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10') | v2_struct_0('#skF_7'('#skF_10')) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_2453])).
% 8.69/2.75  tff(c_2532, plain, (~l1_waybel_0('#skF_12'('#skF_7'('#skF_10')), '#skF_10')), inference(splitLeft, [status(thm)], [c_2531])).
% 8.69/2.75  tff(c_2536, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(resolution, [status(thm)], [c_206, c_2532])).
% 8.69/2.75  tff(c_2539, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_2518, c_2536])).
% 8.69/2.75  tff(c_2540, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_2539])).
% 8.69/2.75  tff(c_2543, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_2540])).
% 8.69/2.75  tff(c_2546, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2543])).
% 8.69/2.75  tff(c_2548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2546])).
% 8.69/2.75  tff(c_2549, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2539])).
% 8.69/2.75  tff(c_2553, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2549, c_68])).
% 8.69/2.75  tff(c_2556, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2553])).
% 8.69/2.75  tff(c_2558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2556])).
% 8.69/2.75  tff(c_2559, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | v2_struct_0('#skF_12'('#skF_7'('#skF_10'))) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2531])).
% 8.69/2.75  tff(c_2577, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_2559])).
% 8.69/2.75  tff(c_2580, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_62, c_2577])).
% 8.69/2.75  tff(c_2583, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2580])).
% 8.69/2.75  tff(c_2585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2583])).
% 8.69/2.75  tff(c_2587, plain, (l1_waybel_0('#skF_7'('#skF_10'), '#skF_10')), inference(splitRight, [status(thm)], [c_2559])).
% 8.69/2.75  tff(c_2586, plain, (v2_struct_0('#skF_7'('#skF_10')) | k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(splitRight, [status(thm)], [c_2559])).
% 8.69/2.75  tff(c_2589, plain, (v2_struct_0('#skF_12'('#skF_7'('#skF_10')))), inference(splitLeft, [status(thm)], [c_2586])).
% 8.69/2.75  tff(c_2592, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(resolution, [status(thm)], [c_2589, c_178])).
% 8.69/2.75  tff(c_2595, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_2518, c_2587, c_2592])).
% 8.69/2.75  tff(c_2598, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2595, c_68])).
% 8.69/2.75  tff(c_2601, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2598])).
% 8.69/2.75  tff(c_2603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2601])).
% 8.69/2.75  tff(c_2604, plain, (k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0 | v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2586])).
% 8.69/2.75  tff(c_2606, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(splitLeft, [status(thm)], [c_2604])).
% 8.69/2.75  tff(c_2667, plain, (v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2606, c_68])).
% 8.69/2.75  tff(c_2670, plain, (v1_compts_1('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2667])).
% 8.69/2.75  tff(c_2672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_132, c_2670])).
% 8.69/2.75  tff(c_2674, plain, (~v2_struct_0('#skF_7'('#skF_10'))), inference(splitRight, [status(thm)], [c_2604])).
% 8.69/2.75  tff(c_2673, plain, (k10_yellow_6('#skF_10', '#skF_12'('#skF_7'('#skF_10')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2604])).
% 8.69/2.75  tff(c_2737, plain, (~l1_waybel_0('#skF_7'('#skF_10'), '#skF_10') | ~v7_waybel_0('#skF_7'('#skF_10')) | ~v4_orders_2('#skF_7'('#skF_10')) | v2_struct_0('#skF_7'('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2673, c_258])).
% 8.69/2.75  tff(c_2814, plain, (v2_struct_0('#skF_7'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_2518, c_2587, c_2737])).
% 8.69/2.75  tff(c_2816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2674, c_2814])).
% 8.69/2.75  tff(c_2817, plain, (~v2_struct_0('#skF_11')), inference(splitRight, [status(thm)], [c_104])).
% 8.69/2.75  tff(c_2818, plain, (v1_compts_1('#skF_10')), inference(splitRight, [status(thm)], [c_104])).
% 8.69/2.75  tff(c_102, plain, (v4_orders_2('#skF_11') | ~v1_compts_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_2819, plain, (~v1_compts_1('#skF_10')), inference(splitLeft, [status(thm)], [c_102])).
% 8.69/2.75  tff(c_2821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2818, c_2819])).
% 8.69/2.75  tff(c_2822, plain, (v4_orders_2('#skF_11')), inference(splitRight, [status(thm)], [c_102])).
% 8.69/2.75  tff(c_100, plain, (v7_waybel_0('#skF_11') | ~v1_compts_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_2827, plain, (v7_waybel_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_100])).
% 8.69/2.75  tff(c_98, plain, (l1_waybel_0('#skF_11', '#skF_10') | ~v1_compts_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_2829, plain, (l1_waybel_0('#skF_11', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_98])).
% 8.69/2.75  tff(c_70, plain, (![A_160, B_167]: (r3_waybel_9(A_160, B_167, '#skF_6'(A_160, B_167)) | ~l1_waybel_0(B_167, A_160) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_72, plain, (![A_160, B_167]: (m1_subset_1('#skF_6'(A_160, B_167), u1_struct_0(A_160)) | ~l1_waybel_0(B_167, A_160) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_265])).
% 8.69/2.75  tff(c_2911, plain, (![A_711, B_712, C_713]: (m2_yellow_6('#skF_5'(A_711, B_712, C_713), A_711, B_712) | ~r3_waybel_9(A_711, B_712, C_713) | ~m1_subset_1(C_713, u1_struct_0(A_711)) | ~l1_waybel_0(B_712, A_711) | ~v7_waybel_0(B_712) | ~v4_orders_2(B_712) | v2_struct_0(B_712) | ~l1_pre_topc(A_711) | ~v2_pre_topc(A_711) | v2_struct_0(A_711))), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.69/2.75  tff(c_34, plain, (![C_98, A_95, B_96]: (l1_waybel_0(C_98, A_95) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_3004, plain, (![A_731, B_732, C_733]: (l1_waybel_0('#skF_5'(A_731, B_732, C_733), A_731) | ~l1_struct_0(A_731) | ~r3_waybel_9(A_731, B_732, C_733) | ~m1_subset_1(C_733, u1_struct_0(A_731)) | ~l1_waybel_0(B_732, A_731) | ~v7_waybel_0(B_732) | ~v4_orders_2(B_732) | v2_struct_0(B_732) | ~l1_pre_topc(A_731) | ~v2_pre_topc(A_731) | v2_struct_0(A_731))), inference(resolution, [status(thm)], [c_2911, c_34])).
% 8.69/2.75  tff(c_3064, plain, (![A_775, B_776, B_777]: (l1_waybel_0('#skF_5'(A_775, B_776, '#skF_6'(A_775, B_777)), A_775) | ~l1_struct_0(A_775) | ~r3_waybel_9(A_775, B_776, '#skF_6'(A_775, B_777)) | ~l1_waybel_0(B_776, A_775) | ~v7_waybel_0(B_776) | ~v4_orders_2(B_776) | v2_struct_0(B_776) | ~l1_waybel_0(B_777, A_775) | ~v7_waybel_0(B_777) | ~v4_orders_2(B_777) | v2_struct_0(B_777) | ~v1_compts_1(A_775) | ~l1_pre_topc(A_775) | ~v2_pre_topc(A_775) | v2_struct_0(A_775))), inference(resolution, [status(thm)], [c_72, c_3004])).
% 8.69/2.75  tff(c_44, plain, (![B_116, A_114]: (v3_yellow_6(B_116, A_114) | k10_yellow_6(A_114, B_116)=k1_xboole_0 | ~l1_waybel_0(B_116, A_114) | ~v7_waybel_0(B_116) | ~v4_orders_2(B_116) | v2_struct_0(B_116) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.69/2.75  tff(c_96, plain, (![C_189]: (~v3_yellow_6(C_189, '#skF_10') | ~m2_yellow_6(C_189, '#skF_10', '#skF_11') | ~v1_compts_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_318])).
% 8.69/2.75  tff(c_2833, plain, (![C_189]: (~v3_yellow_6(C_189, '#skF_10') | ~m2_yellow_6(C_189, '#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2818, c_96])).
% 8.69/2.75  tff(c_2927, plain, (![C_713]: (~v3_yellow_6('#skF_5'('#skF_10', '#skF_11', C_713), '#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', C_713) | ~m1_subset_1(C_713, u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_2911, c_2833])).
% 8.69/2.75  tff(c_2934, plain, (![C_713]: (~v3_yellow_6('#skF_5'('#skF_10', '#skF_11', C_713), '#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', C_713) | ~m1_subset_1(C_713, u1_struct_0('#skF_10')) | v2_struct_0('#skF_11') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2822, c_2827, c_2829, c_2927])).
% 8.69/2.75  tff(c_2936, plain, (![C_714]: (~v3_yellow_6('#skF_5'('#skF_10', '#skF_11', C_714), '#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', C_714) | ~m1_subset_1(C_714, u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_2934])).
% 8.69/2.75  tff(c_2939, plain, (![C_714]: (~r3_waybel_9('#skF_10', '#skF_11', C_714) | ~m1_subset_1(C_714, u1_struct_0('#skF_10')) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', C_714))=k1_xboole_0 | ~l1_waybel_0('#skF_5'('#skF_10', '#skF_11', C_714), '#skF_10') | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', C_714)) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', C_714)) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', C_714)) | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_44, c_2936])).
% 8.69/2.75  tff(c_2942, plain, (![C_714]: (~r3_waybel_9('#skF_10', '#skF_11', C_714) | ~m1_subset_1(C_714, u1_struct_0('#skF_10')) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', C_714))=k1_xboole_0 | ~l1_waybel_0('#skF_5'('#skF_10', '#skF_11', C_714), '#skF_10') | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', C_714)) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', C_714)) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', C_714)) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2939])).
% 8.69/2.75  tff(c_2945, plain, (![C_718]: (~r3_waybel_9('#skF_10', '#skF_11', C_718) | ~m1_subset_1(C_718, u1_struct_0('#skF_10')) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', C_718))=k1_xboole_0 | ~l1_waybel_0('#skF_5'('#skF_10', '#skF_11', C_718), '#skF_10') | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', C_718)) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', C_718)) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', C_718)))), inference(negUnitSimplification, [status(thm)], [c_94, c_2942])).
% 8.69/2.75  tff(c_2953, plain, (![B_167]: (~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~l1_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)), '#skF_10') | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_72, c_2945])).
% 8.69/2.75  tff(c_2960, plain, (![B_167]: (~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~l1_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)), '#skF_10') | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_2953])).
% 8.69/2.75  tff(c_2961, plain, (![B_167]: (~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~l1_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)), '#skF_10') | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167))), inference(negUnitSimplification, [status(thm)], [c_94, c_2960])).
% 8.69/2.75  tff(c_3068, plain, (![B_777]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777)))=k1_xboole_0 | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777)) | ~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~l1_waybel_0(B_777, '#skF_10') | ~v7_waybel_0(B_777) | ~v4_orders_2(B_777) | v2_struct_0(B_777) | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_3064, c_2961])).
% 8.69/2.75  tff(c_3071, plain, (![B_777]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777)))=k1_xboole_0 | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777)) | v2_struct_0('#skF_11') | ~l1_waybel_0(B_777, '#skF_10') | ~v7_waybel_0(B_777) | ~v4_orders_2(B_777) | v2_struct_0(B_777) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_2822, c_2827, c_2829, c_3068])).
% 8.69/2.75  tff(c_3072, plain, (![B_777]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777)))=k1_xboole_0 | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777))) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_777)) | ~l1_waybel_0(B_777, '#skF_10') | ~v7_waybel_0(B_777) | ~v4_orders_2(B_777) | v2_struct_0(B_777))), inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_3071])).
% 8.69/2.75  tff(c_3073, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_3072])).
% 8.69/2.75  tff(c_3076, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_10, c_3073])).
% 8.69/2.75  tff(c_3080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_3076])).
% 8.69/2.75  tff(c_3082, plain, (l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_3072])).
% 8.69/2.75  tff(c_38, plain, (![C_98, A_95, B_96]: (v4_orders_2(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_2969, plain, (![A_722, B_723, C_724]: (v4_orders_2('#skF_5'(A_722, B_723, C_724)) | ~l1_struct_0(A_722) | ~r3_waybel_9(A_722, B_723, C_724) | ~m1_subset_1(C_724, u1_struct_0(A_722)) | ~l1_waybel_0(B_723, A_722) | ~v7_waybel_0(B_723) | ~v4_orders_2(B_723) | v2_struct_0(B_723) | ~l1_pre_topc(A_722) | ~v2_pre_topc(A_722) | v2_struct_0(A_722))), inference(resolution, [status(thm)], [c_2911, c_38])).
% 8.69/2.75  tff(c_2975, plain, (![A_160, B_723, B_167]: (v4_orders_2('#skF_5'(A_160, B_723, '#skF_6'(A_160, B_167))) | ~l1_struct_0(A_160) | ~r3_waybel_9(A_160, B_723, '#skF_6'(A_160, B_167)) | ~l1_waybel_0(B_723, A_160) | ~v7_waybel_0(B_723) | ~v4_orders_2(B_723) | v2_struct_0(B_723) | ~l1_waybel_0(B_167, A_160) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_72, c_2969])).
% 8.69/2.75  tff(c_36, plain, (![C_98, A_95, B_96]: (v7_waybel_0(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_2962, plain, (![A_719, B_720, C_721]: (v7_waybel_0('#skF_5'(A_719, B_720, C_721)) | ~l1_struct_0(A_719) | ~r3_waybel_9(A_719, B_720, C_721) | ~m1_subset_1(C_721, u1_struct_0(A_719)) | ~l1_waybel_0(B_720, A_719) | ~v7_waybel_0(B_720) | ~v4_orders_2(B_720) | v2_struct_0(B_720) | ~l1_pre_topc(A_719) | ~v2_pre_topc(A_719) | v2_struct_0(A_719))), inference(resolution, [status(thm)], [c_2911, c_36])).
% 8.69/2.75  tff(c_2968, plain, (![A_160, B_720, B_167]: (v7_waybel_0('#skF_5'(A_160, B_720, '#skF_6'(A_160, B_167))) | ~l1_struct_0(A_160) | ~r3_waybel_9(A_160, B_720, '#skF_6'(A_160, B_167)) | ~l1_waybel_0(B_720, A_160) | ~v7_waybel_0(B_720) | ~v4_orders_2(B_720) | v2_struct_0(B_720) | ~l1_waybel_0(B_167, A_160) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1(A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_72, c_2962])).
% 8.69/2.75  tff(c_3106, plain, (![B_800]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_800)))=k1_xboole_0 | ~v7_waybel_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_800))) | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_800))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_800))) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_800)) | ~l1_waybel_0(B_800, '#skF_10') | ~v7_waybel_0(B_800) | ~v4_orders_2(B_800) | v2_struct_0(B_800))), inference(splitRight, [status(thm)], [c_3072])).
% 8.69/2.75  tff(c_3110, plain, (![B_167]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | ~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_2968, c_3106])).
% 8.69/2.75  tff(c_3113, plain, (![B_167]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | v2_struct_0('#skF_11') | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_2822, c_2827, c_2829, c_3082, c_3110])).
% 8.69/2.75  tff(c_3115, plain, (![B_801]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_801)))=k1_xboole_0 | ~v4_orders_2('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_801))) | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_801))) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_801)) | ~l1_waybel_0(B_801, '#skF_10') | ~v7_waybel_0(B_801) | ~v4_orders_2(B_801) | v2_struct_0(B_801))), inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_3113])).
% 8.69/2.75  tff(c_3119, plain, (![B_167]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~l1_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | ~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_2975, c_3115])).
% 8.69/2.75  tff(c_3122, plain, (![B_167]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167))) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | v2_struct_0('#skF_11') | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_2822, c_2827, c_2829, c_3082, c_3119])).
% 8.69/2.75  tff(c_3124, plain, (![B_802]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802)))=k1_xboole_0 | v2_struct_0('#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802))) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802)) | ~l1_waybel_0(B_802, '#skF_10') | ~v7_waybel_0(B_802) | ~v4_orders_2(B_802) | v2_struct_0(B_802))), inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_3122])).
% 8.69/2.75  tff(c_40, plain, (![C_98, A_95, B_96]: (~v2_struct_0(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.69/2.75  tff(c_2929, plain, (![A_711, B_712, C_713]: (~v2_struct_0('#skF_5'(A_711, B_712, C_713)) | ~l1_struct_0(A_711) | ~r3_waybel_9(A_711, B_712, C_713) | ~m1_subset_1(C_713, u1_struct_0(A_711)) | ~l1_waybel_0(B_712, A_711) | ~v7_waybel_0(B_712) | ~v4_orders_2(B_712) | v2_struct_0(B_712) | ~l1_pre_topc(A_711) | ~v2_pre_topc(A_711) | v2_struct_0(A_711))), inference(resolution, [status(thm)], [c_2911, c_40])).
% 8.69/2.75  tff(c_3126, plain, (![B_802]: (~l1_struct_0('#skF_10') | ~m1_subset_1('#skF_6'('#skF_10', B_802), u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802)))=k1_xboole_0 | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802)) | ~l1_waybel_0(B_802, '#skF_10') | ~v7_waybel_0(B_802) | ~v4_orders_2(B_802) | v2_struct_0(B_802))), inference(resolution, [status(thm)], [c_3124, c_2929])).
% 8.69/2.75  tff(c_3129, plain, (![B_802]: (~m1_subset_1('#skF_6'('#skF_10', B_802), u1_struct_0('#skF_10')) | v2_struct_0('#skF_11') | v2_struct_0('#skF_10') | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802)))=k1_xboole_0 | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_802)) | ~l1_waybel_0(B_802, '#skF_10') | ~v7_waybel_0(B_802) | ~v4_orders_2(B_802) | v2_struct_0(B_802))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2822, c_2827, c_2829, c_3082, c_3126])).
% 8.69/2.75  tff(c_3131, plain, (![B_803]: (~m1_subset_1('#skF_6'('#skF_10', B_803), u1_struct_0('#skF_10')) | k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_803)))=k1_xboole_0 | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_803)) | ~l1_waybel_0(B_803, '#skF_10') | ~v7_waybel_0(B_803) | ~v4_orders_2(B_803) | v2_struct_0(B_803))), inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_3129])).
% 8.69/2.75  tff(c_3135, plain, (![B_167]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_72, c_3131])).
% 8.69/2.75  tff(c_3138, plain, (![B_167]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)))=k1_xboole_0 | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_3135])).
% 8.69/2.75  tff(c_3140, plain, (![B_804]: (k10_yellow_6('#skF_10', '#skF_5'('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_804)))=k1_xboole_0 | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_804)) | ~l1_waybel_0(B_804, '#skF_10') | ~v7_waybel_0(B_804) | ~v4_orders_2(B_804) | v2_struct_0(B_804))), inference(negUnitSimplification, [status(thm)], [c_94, c_3138])).
% 8.69/2.75  tff(c_2976, plain, (![C_725, A_726, B_727]: (r2_hidden(C_725, k10_yellow_6(A_726, '#skF_5'(A_726, B_727, C_725))) | ~r3_waybel_9(A_726, B_727, C_725) | ~m1_subset_1(C_725, u1_struct_0(A_726)) | ~l1_waybel_0(B_727, A_726) | ~v7_waybel_0(B_727) | ~v4_orders_2(B_727) | v2_struct_0(B_727) | ~l1_pre_topc(A_726) | ~v2_pre_topc(A_726) | v2_struct_0(A_726))), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.69/2.75  tff(c_2988, plain, (![A_726, B_727, C_725]: (~r1_tarski(k10_yellow_6(A_726, '#skF_5'(A_726, B_727, C_725)), C_725) | ~r3_waybel_9(A_726, B_727, C_725) | ~m1_subset_1(C_725, u1_struct_0(A_726)) | ~l1_waybel_0(B_727, A_726) | ~v7_waybel_0(B_727) | ~v4_orders_2(B_727) | v2_struct_0(B_727) | ~l1_pre_topc(A_726) | ~v2_pre_topc(A_726) | v2_struct_0(A_726))), inference(resolution, [status(thm)], [c_2976, c_8])).
% 8.69/2.75  tff(c_3154, plain, (![B_804]: (~r1_tarski(k1_xboole_0, '#skF_6'('#skF_10', B_804)) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_804)) | ~m1_subset_1('#skF_6'('#skF_10', B_804), u1_struct_0('#skF_10')) | ~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_804)) | ~l1_waybel_0(B_804, '#skF_10') | ~v7_waybel_0(B_804) | ~v4_orders_2(B_804) | v2_struct_0(B_804))), inference(superposition, [status(thm), theory('equality')], [c_3140, c_2988])).
% 8.69/2.75  tff(c_3181, plain, (![B_804]: (~m1_subset_1('#skF_6'('#skF_10', B_804), u1_struct_0('#skF_10')) | v2_struct_0('#skF_11') | v2_struct_0('#skF_10') | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_804)) | ~l1_waybel_0(B_804, '#skF_10') | ~v7_waybel_0(B_804) | ~v4_orders_2(B_804) | v2_struct_0(B_804))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2822, c_2827, c_2829, c_2, c_3154])).
% 8.69/2.75  tff(c_3196, plain, (![B_805]: (~m1_subset_1('#skF_6'('#skF_10', B_805), u1_struct_0('#skF_10')) | ~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_805)) | ~l1_waybel_0(B_805, '#skF_10') | ~v7_waybel_0(B_805) | ~v4_orders_2(B_805) | v2_struct_0(B_805))), inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_3181])).
% 8.69/2.75  tff(c_3200, plain, (![B_167]: (~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_72, c_3196])).
% 8.69/2.75  tff(c_3203, plain, (![B_167]: (~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_167)) | ~l1_waybel_0(B_167, '#skF_10') | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_3200])).
% 8.69/2.75  tff(c_3205, plain, (![B_806]: (~r3_waybel_9('#skF_10', '#skF_11', '#skF_6'('#skF_10', B_806)) | ~l1_waybel_0(B_806, '#skF_10') | ~v7_waybel_0(B_806) | ~v4_orders_2(B_806) | v2_struct_0(B_806))), inference(negUnitSimplification, [status(thm)], [c_94, c_3203])).
% 8.69/2.75  tff(c_3209, plain, (~l1_waybel_0('#skF_11', '#skF_10') | ~v7_waybel_0('#skF_11') | ~v4_orders_2('#skF_11') | v2_struct_0('#skF_11') | ~v1_compts_1('#skF_10') | ~l1_pre_topc('#skF_10') | ~v2_pre_topc('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_70, c_3205])).
% 8.69/2.75  tff(c_3212, plain, (v2_struct_0('#skF_11') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_2818, c_2822, c_2827, c_2829, c_3209])).
% 8.69/2.75  tff(c_3214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_2817, c_3212])).
% 8.69/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.69/2.75  
% 8.69/2.75  Inference rules
% 8.69/2.75  ----------------------
% 8.69/2.75  #Ref     : 0
% 8.69/2.75  #Sup     : 572
% 8.69/2.75  #Fact    : 2
% 8.69/2.75  #Define  : 0
% 8.69/2.75  #Split   : 48
% 8.69/2.75  #Chain   : 0
% 8.69/2.75  #Close   : 0
% 8.69/2.75  
% 8.69/2.75  Ordering : KBO
% 8.69/2.75  
% 8.69/2.75  Simplification rules
% 8.69/2.75  ----------------------
% 8.69/2.75  #Subsume      : 126
% 8.69/2.75  #Demod        : 880
% 8.69/2.75  #Tautology    : 62
% 8.69/2.75  #SimpNegUnit  : 177
% 8.69/2.75  #BackRed      : 0
% 8.69/2.75  
% 8.69/2.75  #Partial instantiations: 0
% 8.69/2.75  #Strategies tried      : 1
% 8.69/2.75  
% 8.69/2.75  Timing (in seconds)
% 8.69/2.75  ----------------------
% 8.90/2.76  Preprocessing        : 0.40
% 8.90/2.76  Parsing              : 0.21
% 8.90/2.76  CNF conversion       : 0.04
% 8.90/2.76  Main loop            : 1.47
% 8.90/2.76  Inferencing          : 0.57
% 8.90/2.76  Reduction            : 0.40
% 8.90/2.76  Demodulation         : 0.27
% 8.90/2.76  BG Simplification    : 0.06
% 8.90/2.76  Subsumption          : 0.36
% 8.90/2.76  Abstraction          : 0.06
% 8.90/2.76  MUC search           : 0.00
% 8.90/2.76  Cooper               : 0.00
% 8.90/2.76  Total                : 2.02
% 8.90/2.76  Index Insertion      : 0.00
% 8.90/2.76  Index Deletion       : 0.00
% 8.90/2.76  Index Matching       : 0.00
% 8.90/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
