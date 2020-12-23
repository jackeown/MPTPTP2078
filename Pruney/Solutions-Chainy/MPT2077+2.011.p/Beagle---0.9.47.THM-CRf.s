%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:41 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  257 (3574 expanded)
%              Number of leaves         :   48 (1184 expanded)
%              Depth                    :   37
%              Number of atoms          : 1323 (24786 expanded)
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

tff(f_301,negated_conjecture,(
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

tff(f_276,axiom,(
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

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

tff(f_248,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_90,plain,
    ( ~ v2_struct_0('#skF_9')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_117,plain,(
    ~ v1_compts_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_78,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_76,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_68,plain,(
    ! [A_145] :
      ( v4_orders_2('#skF_7'(A_145))
      | v1_compts_1(A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_116,plain,(
    ! [B_164] :
      ( v1_compts_1('#skF_8')
      | m2_yellow_6('#skF_10'(B_164),'#skF_8',B_164)
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_158,plain,(
    ! [B_164] :
      ( m2_yellow_6('#skF_10'(B_164),'#skF_8',B_164)
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_116])).

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

tff(c_121,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(A_170,B_171)
      | ~ m1_subset_1(A_170,k1_zfmisc_1(B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_121])).

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

tff(c_356,plain,(
    ! [A_280,B_281,D_282] :
      ( m1_connsp_2('#skF_1'(A_280,B_281,k10_yellow_6(A_280,B_281),D_282),A_280,D_282)
      | r2_hidden(D_282,k10_yellow_6(A_280,B_281))
      | ~ m1_subset_1(D_282,u1_struct_0(A_280))
      | ~ m1_subset_1(k10_yellow_6(A_280,B_281),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_waybel_0(B_281,A_280)
      | ~ v7_waybel_0(B_281)
      | ~ v4_orders_2(B_281)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_362,plain,(
    ! [A_94,B_95,D_282] :
      ( m1_connsp_2('#skF_1'(A_94,B_95,k10_yellow_6(A_94,B_95),D_282),A_94,D_282)
      | r2_hidden(D_282,k10_yellow_6(A_94,B_95))
      | ~ m1_subset_1(D_282,u1_struct_0(A_94))
      | ~ l1_waybel_0(B_95,A_94)
      | ~ v7_waybel_0(B_95)
      | ~ v4_orders_2(B_95)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_34,c_356])).

tff(c_368,plain,(
    ! [A_286,B_287,C_288,E_289] :
      ( r2_hidden('#skF_2'(A_286,B_287,C_288),C_288)
      | r1_waybel_0(A_286,B_287,E_289)
      | ~ m1_connsp_2(E_289,A_286,'#skF_2'(A_286,B_287,C_288))
      | k10_yellow_6(A_286,B_287) = C_288
      | ~ m1_subset_1(C_288,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_waybel_0(B_287,A_286)
      | ~ v7_waybel_0(B_287)
      | ~ v4_orders_2(B_287)
      | v2_struct_0(B_287)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_520,plain,(
    ! [A_413,B_414,C_415,B_416] :
      ( r2_hidden('#skF_2'(A_413,B_414,C_415),C_415)
      | r1_waybel_0(A_413,B_414,'#skF_1'(A_413,B_416,k10_yellow_6(A_413,B_416),'#skF_2'(A_413,B_414,C_415)))
      | k10_yellow_6(A_413,B_414) = C_415
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_waybel_0(B_414,A_413)
      | ~ v7_waybel_0(B_414)
      | ~ v4_orders_2(B_414)
      | v2_struct_0(B_414)
      | r2_hidden('#skF_2'(A_413,B_414,C_415),k10_yellow_6(A_413,B_416))
      | ~ m1_subset_1('#skF_2'(A_413,B_414,C_415),u1_struct_0(A_413))
      | ~ l1_waybel_0(B_416,A_413)
      | ~ v7_waybel_0(B_416)
      | ~ v4_orders_2(B_416)
      | v2_struct_0(B_416)
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | v2_struct_0(A_413) ) ),
    inference(resolution,[status(thm)],[c_362,c_368])).

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

tff(c_547,plain,(
    ! [A_417,B_418,C_419] :
      ( ~ m1_subset_1(k10_yellow_6(A_417,B_418),k1_zfmisc_1(u1_struct_0(A_417)))
      | r2_hidden('#skF_2'(A_417,B_418,C_419),C_419)
      | k10_yellow_6(A_417,B_418) = C_419
      | ~ m1_subset_1(C_419,k1_zfmisc_1(u1_struct_0(A_417)))
      | r2_hidden('#skF_2'(A_417,B_418,C_419),k10_yellow_6(A_417,B_418))
      | ~ m1_subset_1('#skF_2'(A_417,B_418,C_419),u1_struct_0(A_417))
      | ~ l1_waybel_0(B_418,A_417)
      | ~ v7_waybel_0(B_418)
      | ~ v4_orders_2(B_418)
      | v2_struct_0(B_418)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(resolution,[status(thm)],[c_520,c_30])).

tff(c_571,plain,(
    ! [A_420,B_421,C_422] :
      ( r2_hidden('#skF_2'(A_420,B_421,C_422),C_422)
      | k10_yellow_6(A_420,B_421) = C_422
      | ~ m1_subset_1(C_422,k1_zfmisc_1(u1_struct_0(A_420)))
      | r2_hidden('#skF_2'(A_420,B_421,C_422),k10_yellow_6(A_420,B_421))
      | ~ m1_subset_1('#skF_2'(A_420,B_421,C_422),u1_struct_0(A_420))
      | ~ l1_waybel_0(B_421,A_420)
      | ~ v7_waybel_0(B_421)
      | ~ v4_orders_2(B_421)
      | v2_struct_0(B_421)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(resolution,[status(thm)],[c_34,c_547])).

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

tff(c_612,plain,(
    ! [A_423,B_424,C_425] :
      ( r3_waybel_9(A_423,B_424,'#skF_2'(A_423,B_424,C_425))
      | r2_hidden('#skF_2'(A_423,B_424,C_425),C_425)
      | k10_yellow_6(A_423,B_424) = C_425
      | ~ m1_subset_1(C_425,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_subset_1('#skF_2'(A_423,B_424,C_425),u1_struct_0(A_423))
      | ~ l1_waybel_0(B_424,A_423)
      | ~ v7_waybel_0(B_424)
      | ~ v4_orders_2(B_424)
      | v2_struct_0(B_424)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_571,c_48])).

tff(c_616,plain,(
    ! [A_426,B_427,C_428] :
      ( r3_waybel_9(A_426,B_427,'#skF_2'(A_426,B_427,C_428))
      | r2_hidden('#skF_2'(A_426,B_427,C_428),C_428)
      | k10_yellow_6(A_426,B_427) = C_428
      | ~ m1_subset_1(C_428,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_waybel_0(B_427,A_426)
      | ~ v7_waybel_0(B_427)
      | ~ v4_orders_2(B_427)
      | v2_struct_0(B_427)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(resolution,[status(thm)],[c_14,c_612])).

tff(c_651,plain,(
    ! [A_435,B_436,A_437] :
      ( r3_waybel_9(A_435,B_436,'#skF_2'(A_435,B_436,A_437))
      | r2_hidden('#skF_2'(A_435,B_436,A_437),A_437)
      | k10_yellow_6(A_435,B_436) = A_437
      | ~ l1_waybel_0(B_436,A_435)
      | ~ v7_waybel_0(B_436)
      | ~ v4_orders_2(B_436)
      | v2_struct_0(B_436)
      | ~ l1_pre_topc(A_435)
      | ~ v2_pre_topc(A_435)
      | v2_struct_0(A_435)
      | ~ r1_tarski(A_437,u1_struct_0(A_435)) ) ),
    inference(resolution,[status(thm)],[c_6,c_616])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_682,plain,(
    ! [A_438,A_439,B_440] :
      ( ~ r1_tarski(A_438,'#skF_2'(A_439,B_440,A_438))
      | r3_waybel_9(A_439,B_440,'#skF_2'(A_439,B_440,A_438))
      | k10_yellow_6(A_439,B_440) = A_438
      | ~ l1_waybel_0(B_440,A_439)
      | ~ v7_waybel_0(B_440)
      | ~ v4_orders_2(B_440)
      | v2_struct_0(B_440)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439)
      | ~ r1_tarski(A_438,u1_struct_0(A_439)) ) ),
    inference(resolution,[status(thm)],[c_651,c_10])).

tff(c_685,plain,(
    ! [A_439,B_440] :
      ( r3_waybel_9(A_439,B_440,'#skF_2'(A_439,B_440,k1_xboole_0))
      | k10_yellow_6(A_439,B_440) = k1_xboole_0
      | ~ l1_waybel_0(B_440,A_439)
      | ~ v7_waybel_0(B_440)
      | ~ v4_orders_2(B_440)
      | v2_struct_0(B_440)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_439)) ) ),
    inference(resolution,[status(thm)],[c_125,c_682])).

tff(c_689,plain,(
    ! [A_441,B_442] :
      ( r3_waybel_9(A_441,B_442,'#skF_2'(A_441,B_442,k1_xboole_0))
      | k10_yellow_6(A_441,B_442) = k1_xboole_0
      | ~ l1_waybel_0(B_442,A_441)
      | ~ v7_waybel_0(B_442)
      | ~ v4_orders_2(B_442)
      | v2_struct_0(B_442)
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441)
      | v2_struct_0(A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_685])).

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

tff(c_1168,plain,(
    ! [A_510,B_511,B_512] :
      ( r3_waybel_9(A_510,B_511,'#skF_2'(A_510,B_512,k1_xboole_0))
      | ~ m1_subset_1('#skF_2'(A_510,B_512,k1_xboole_0),u1_struct_0(A_510))
      | ~ m2_yellow_6(B_512,A_510,B_511)
      | ~ l1_waybel_0(B_511,A_510)
      | ~ v7_waybel_0(B_511)
      | ~ v4_orders_2(B_511)
      | v2_struct_0(B_511)
      | k10_yellow_6(A_510,B_512) = k1_xboole_0
      | ~ l1_waybel_0(B_512,A_510)
      | ~ v7_waybel_0(B_512)
      | ~ v4_orders_2(B_512)
      | v2_struct_0(B_512)
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(resolution,[status(thm)],[c_689,c_50])).

tff(c_1177,plain,(
    ! [A_10,B_511,B_54] :
      ( r3_waybel_9(A_10,B_511,'#skF_2'(A_10,B_54,k1_xboole_0))
      | ~ m2_yellow_6(B_54,A_10,B_511)
      | ~ l1_waybel_0(B_511,A_10)
      | ~ v7_waybel_0(B_511)
      | ~ v4_orders_2(B_511)
      | v2_struct_0(B_511)
      | k10_yellow_6(A_10,B_54) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_waybel_0(B_54,A_10)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_1168])).

tff(c_1187,plain,(
    ! [A_513,B_514,B_515] :
      ( r3_waybel_9(A_513,B_514,'#skF_2'(A_513,B_515,k1_xboole_0))
      | ~ m2_yellow_6(B_515,A_513,B_514)
      | ~ l1_waybel_0(B_514,A_513)
      | ~ v7_waybel_0(B_514)
      | ~ v4_orders_2(B_514)
      | v2_struct_0(B_514)
      | k10_yellow_6(A_513,B_515) = k1_xboole_0
      | ~ l1_waybel_0(B_515,A_513)
      | ~ v7_waybel_0(B_515)
      | ~ v4_orders_2(B_515)
      | v2_struct_0(B_515)
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1177])).

tff(c_60,plain,(
    ! [A_145,C_155] :
      ( ~ r3_waybel_9(A_145,'#skF_7'(A_145),C_155)
      | ~ m1_subset_1(C_155,u1_struct_0(A_145))
      | v1_compts_1(A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_1214,plain,(
    ! [A_519,B_520] :
      ( ~ m1_subset_1('#skF_2'(A_519,B_520,k1_xboole_0),u1_struct_0(A_519))
      | v1_compts_1(A_519)
      | ~ m2_yellow_6(B_520,A_519,'#skF_7'(A_519))
      | ~ l1_waybel_0('#skF_7'(A_519),A_519)
      | ~ v7_waybel_0('#skF_7'(A_519))
      | ~ v4_orders_2('#skF_7'(A_519))
      | v2_struct_0('#skF_7'(A_519))
      | k10_yellow_6(A_519,B_520) = k1_xboole_0
      | ~ l1_waybel_0(B_520,A_519)
      | ~ v7_waybel_0(B_520)
      | ~ v4_orders_2(B_520)
      | v2_struct_0(B_520)
      | ~ l1_pre_topc(A_519)
      | ~ v2_pre_topc(A_519)
      | v2_struct_0(A_519) ) ),
    inference(resolution,[status(thm)],[c_1187,c_60])).

tff(c_1226,plain,(
    ! [A_10,B_54] :
      ( v1_compts_1(A_10)
      | ~ m2_yellow_6(B_54,A_10,'#skF_7'(A_10))
      | ~ l1_waybel_0('#skF_7'(A_10),A_10)
      | ~ v7_waybel_0('#skF_7'(A_10))
      | ~ v4_orders_2('#skF_7'(A_10))
      | v2_struct_0('#skF_7'(A_10))
      | k10_yellow_6(A_10,B_54) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_waybel_0(B_54,A_10)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_1214])).

tff(c_1288,plain,(
    ! [A_526,B_527] :
      ( v1_compts_1(A_526)
      | ~ m2_yellow_6(B_527,A_526,'#skF_7'(A_526))
      | ~ l1_waybel_0('#skF_7'(A_526),A_526)
      | ~ v7_waybel_0('#skF_7'(A_526))
      | ~ v4_orders_2('#skF_7'(A_526))
      | v2_struct_0('#skF_7'(A_526))
      | k10_yellow_6(A_526,B_527) = k1_xboole_0
      | ~ l1_waybel_0(B_527,A_526)
      | ~ v7_waybel_0(B_527)
      | ~ v4_orders_2(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_526)
      | ~ v2_pre_topc(A_526)
      | v2_struct_0(A_526) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1226])).

tff(c_1296,plain,
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
    inference(resolution,[status(thm)],[c_158,c_1288])).

tff(c_1300,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1296])).

tff(c_1301,plain,
    ( k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8')
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1300])).

tff(c_1302,plain,(
    ~ v4_orders_2('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1301])).

tff(c_1305,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_1302])).

tff(c_1308,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1305])).

tff(c_1310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1308])).

tff(c_1312,plain,(
    v4_orders_2('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1301])).

tff(c_66,plain,(
    ! [A_145] :
      ( v7_waybel_0('#skF_7'(A_145))
      | v1_compts_1(A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_64,plain,(
    ! [A_145] :
      ( l1_waybel_0('#skF_7'(A_145),A_145)
      | v1_compts_1(A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_162,plain,(
    ! [C_195,A_196,B_197] :
      ( ~ v2_struct_0(C_195)
      | ~ m2_yellow_6(C_195,A_196,B_197)
      | ~ l1_waybel_0(B_197,A_196)
      | ~ v7_waybel_0(B_197)
      | ~ v4_orders_2(B_197)
      | v2_struct_0(B_197)
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_165,plain,(
    ! [B_164] :
      ( ~ v2_struct_0('#skF_10'(B_164))
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_158,c_162])).

tff(c_168,plain,(
    ! [B_164] :
      ( ~ v2_struct_0('#skF_10'(B_164))
      | ~ l1_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_165])).

tff(c_169,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_172,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_172])).

tff(c_178,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_198,plain,(
    ! [C_207,A_208,B_209] :
      ( l1_waybel_0(C_207,A_208)
      | ~ m2_yellow_6(C_207,A_208,B_209)
      | ~ l1_waybel_0(B_209,A_208)
      | ~ v7_waybel_0(B_209)
      | ~ v4_orders_2(B_209)
      | v2_struct_0(B_209)
      | ~ l1_struct_0(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_201,plain,(
    ! [B_164] :
      ( l1_waybel_0('#skF_10'(B_164),'#skF_8')
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_158,c_198])).

tff(c_204,plain,(
    ! [B_164] :
      ( l1_waybel_0('#skF_10'(B_164),'#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_201])).

tff(c_205,plain,(
    ! [B_164] :
      ( l1_waybel_0('#skF_10'(B_164),'#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_204])).

tff(c_1311,plain,
    ( ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8')
    | v2_struct_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1301])).

tff(c_1313,plain,(
    ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1311])).

tff(c_1316,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_205,c_1313])).

tff(c_1319,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1316])).

tff(c_1320,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1319])).

tff(c_1323,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_1320])).

tff(c_1326,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1323])).

tff(c_1328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1326])).

tff(c_1329,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1319])).

tff(c_1362,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1329])).

tff(c_1365,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_1362])).

tff(c_1368,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1365])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1368])).

tff(c_1371,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1329])).

tff(c_70,plain,(
    ! [A_145] :
      ( ~ v2_struct_0('#skF_7'(A_145))
      | v1_compts_1(A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_1375,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1371,c_70])).

tff(c_1378,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1375])).

tff(c_1380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1378])).

tff(c_1381,plain,
    ( ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1311])).

tff(c_1383,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1381])).

tff(c_1386,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_1383])).

tff(c_1389,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1386])).

tff(c_1391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1389])).

tff(c_1393,plain,(
    v7_waybel_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1381])).

tff(c_188,plain,(
    ! [C_202,A_203,B_204] :
      ( v7_waybel_0(C_202)
      | ~ m2_yellow_6(C_202,A_203,B_204)
      | ~ l1_waybel_0(B_204,A_203)
      | ~ v7_waybel_0(B_204)
      | ~ v4_orders_2(B_204)
      | v2_struct_0(B_204)
      | ~ l1_struct_0(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_191,plain,(
    ! [B_164] :
      ( v7_waybel_0('#skF_10'(B_164))
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_158,c_188])).

tff(c_194,plain,(
    ! [B_164] :
      ( v7_waybel_0('#skF_10'(B_164))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_191])).

tff(c_195,plain,(
    ! [B_164] :
      ( v7_waybel_0('#skF_10'(B_164))
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_194])).

tff(c_1392,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1381])).

tff(c_1394,plain,(
    ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_1392])).

tff(c_1397,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_195,c_1394])).

tff(c_1400,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1393,c_1397])).

tff(c_1432,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1400])).

tff(c_1435,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_1432])).

tff(c_1438,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1435])).

tff(c_1440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1438])).

tff(c_1441,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1400])).

tff(c_1445,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1441,c_70])).

tff(c_1448,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1445])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1448])).

tff(c_1451,plain,
    ( ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1392])).

tff(c_1453,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1451])).

tff(c_1456,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_1453])).

tff(c_1459,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1456])).

tff(c_1461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1459])).

tff(c_1463,plain,(
    l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1451])).

tff(c_180,plain,(
    ! [C_199,A_200,B_201] :
      ( v4_orders_2(C_199)
      | ~ m2_yellow_6(C_199,A_200,B_201)
      | ~ l1_waybel_0(B_201,A_200)
      | ~ v7_waybel_0(B_201)
      | ~ v4_orders_2(B_201)
      | v2_struct_0(B_201)
      | ~ l1_struct_0(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_183,plain,(
    ! [B_164] :
      ( v4_orders_2('#skF_10'(B_164))
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_158,c_180])).

tff(c_186,plain,(
    ! [B_164] :
      ( v4_orders_2('#skF_10'(B_164))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_183])).

tff(c_187,plain,(
    ! [B_164] :
      ( v4_orders_2('#skF_10'(B_164))
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_186])).

tff(c_1462,plain,
    ( ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1451])).

tff(c_1464,plain,(
    ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_1462])).

tff(c_1467,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_187,c_1464])).

tff(c_1470,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1393,c_1463,c_1467])).

tff(c_1504,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1470,c_70])).

tff(c_1507,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1504])).

tff(c_1509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1507])).

tff(c_1510,plain,
    ( k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1462])).

tff(c_1512,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1510])).

tff(c_1515,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1512,c_70])).

tff(c_1518,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1515])).

tff(c_1520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_117,c_1518])).

tff(c_1522,plain,(
    ~ v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1510])).

tff(c_1521,plain,
    ( v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1510])).

tff(c_1523,plain,(
    k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1521])).

tff(c_104,plain,(
    ! [B_164] :
      ( v1_compts_1('#skF_8')
      | v3_yellow_6('#skF_10'(B_164),'#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_154,plain,(
    ! [B_164] :
      ( v3_yellow_6('#skF_10'(B_164),'#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_104])).

tff(c_216,plain,(
    ! [A_215,B_216] :
      ( k10_yellow_6(A_215,B_216) != k1_xboole_0
      | ~ v3_yellow_6(B_216,A_215)
      | ~ l1_waybel_0(B_216,A_215)
      | ~ v7_waybel_0(B_216)
      | ~ v4_orders_2(B_216)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_219,plain,(
    ! [B_164] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_164)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_10'(B_164),'#skF_8')
      | ~ v7_waybel_0('#skF_10'(B_164))
      | ~ v4_orders_2('#skF_10'(B_164))
      | v2_struct_0('#skF_10'(B_164))
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_154,c_216])).

tff(c_222,plain,(
    ! [B_164] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_164)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_10'(B_164),'#skF_8')
      | ~ v7_waybel_0('#skF_10'(B_164))
      | ~ v4_orders_2('#skF_10'(B_164))
      | v2_struct_0('#skF_10'(B_164))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_219])).

tff(c_243,plain,(
    ! [B_228] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_228)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_10'(B_228),'#skF_8')
      | ~ v7_waybel_0('#skF_10'(B_228))
      | ~ v4_orders_2('#skF_10'(B_228))
      | v2_struct_0('#skF_10'(B_228))
      | ~ l1_waybel_0(B_228,'#skF_8')
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_222])).

tff(c_248,plain,(
    ! [B_229] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_229)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_10'(B_229))
      | ~ v4_orders_2('#skF_10'(B_229))
      | v2_struct_0('#skF_10'(B_229))
      | ~ l1_waybel_0(B_229,'#skF_8')
      | ~ v7_waybel_0(B_229)
      | ~ v4_orders_2(B_229)
      | v2_struct_0(B_229) ) ),
    inference(resolution,[status(thm)],[c_205,c_243])).

tff(c_253,plain,(
    ! [B_230] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_230)) != k1_xboole_0
      | ~ v4_orders_2('#skF_10'(B_230))
      | v2_struct_0('#skF_10'(B_230))
      | ~ l1_waybel_0(B_230,'#skF_8')
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230) ) ),
    inference(resolution,[status(thm)],[c_195,c_248])).

tff(c_258,plain,(
    ! [B_231] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_231)) != k1_xboole_0
      | v2_struct_0('#skF_10'(B_231))
      | ~ l1_waybel_0(B_231,'#skF_8')
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231) ) ),
    inference(resolution,[status(thm)],[c_187,c_253])).

tff(c_177,plain,(
    ! [B_164] :
      ( ~ v2_struct_0('#skF_10'(B_164))
      | ~ l1_waybel_0(B_164,'#skF_8')
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164) ) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_262,plain,(
    ! [B_231] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_231)) != k1_xboole_0
      | ~ l1_waybel_0(B_231,'#skF_8')
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231) ) ),
    inference(resolution,[status(thm)],[c_258,c_177])).

tff(c_1573,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_262])).

tff(c_1638,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1393,c_1463,c_1573])).

tff(c_1640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_1638])).

tff(c_1641,plain,(
    v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_1645,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1641,c_177])).

tff(c_1648,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1393,c_1463,c_1645])).

tff(c_1650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_1648])).

tff(c_1651,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_1652,plain,(
    v1_compts_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( v4_orders_2('#skF_9')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1658,plain,(
    v4_orders_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_88])).

tff(c_86,plain,
    ( v7_waybel_0('#skF_9')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1655,plain,(
    v7_waybel_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_86])).

tff(c_84,plain,
    ( l1_waybel_0('#skF_9','#skF_8')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1660,plain,(
    l1_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_84])).

tff(c_56,plain,(
    ! [A_139,B_143] :
      ( r3_waybel_9(A_139,B_143,'#skF_5'(A_139,B_143))
      | ~ l1_waybel_0(B_143,A_139)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_58,plain,(
    ! [A_139,B_143] :
      ( m1_subset_1('#skF_5'(A_139,B_143),u1_struct_0(A_139))
      | ~ l1_waybel_0(B_143,A_139)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1662,plain,(
    ! [A_547,B_548] :
      ( r1_tarski(A_547,B_548)
      | ~ m1_subset_1(A_547,k1_zfmisc_1(B_548)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1666,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_1662])).

tff(c_1743,plain,(
    ! [A_605,B_606,C_607] :
      ( m2_yellow_6('#skF_4'(A_605,B_606,C_607),A_605,B_606)
      | ~ r3_waybel_9(A_605,B_606,C_607)
      | ~ m1_subset_1(C_607,u1_struct_0(A_605))
      | ~ l1_waybel_0(B_606,A_605)
      | ~ v7_waybel_0(B_606)
      | ~ v4_orders_2(B_606)
      | v2_struct_0(B_606)
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
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

tff(c_1846,plain,(
    ! [A_629,B_630,C_631] :
      ( l1_waybel_0('#skF_4'(A_629,B_630,C_631),A_629)
      | ~ l1_struct_0(A_629)
      | ~ r3_waybel_9(A_629,B_630,C_631)
      | ~ m1_subset_1(C_631,u1_struct_0(A_629))
      | ~ l1_waybel_0(B_630,A_629)
      | ~ v7_waybel_0(B_630)
      | ~ v4_orders_2(B_630)
      | v2_struct_0(B_630)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(resolution,[status(thm)],[c_1743,c_36])).

tff(c_1913,plain,(
    ! [A_680,B_681,B_682] :
      ( l1_waybel_0('#skF_4'(A_680,B_681,'#skF_5'(A_680,B_682)),A_680)
      | ~ l1_struct_0(A_680)
      | ~ r3_waybel_9(A_680,B_681,'#skF_5'(A_680,B_682))
      | ~ l1_waybel_0(B_681,A_680)
      | ~ v7_waybel_0(B_681)
      | ~ v4_orders_2(B_681)
      | v2_struct_0(B_681)
      | ~ l1_waybel_0(B_682,A_680)
      | ~ v7_waybel_0(B_682)
      | ~ v4_orders_2(B_682)
      | v2_struct_0(B_682)
      | ~ v1_compts_1(A_680)
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(resolution,[status(thm)],[c_58,c_1846])).

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

tff(c_82,plain,(
    ! [C_163] :
      ( ~ v3_yellow_6(C_163,'#skF_8')
      | ~ m2_yellow_6(C_163,'#skF_8','#skF_9')
      | ~ v1_compts_1('#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1674,plain,(
    ! [C_163] :
      ( ~ v3_yellow_6(C_163,'#skF_8')
      | ~ m2_yellow_6(C_163,'#skF_8','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_82])).

tff(c_1759,plain,(
    ! [C_607] :
      ( ~ v3_yellow_6('#skF_4'('#skF_8','#skF_9',C_607),'#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9',C_607)
      | ~ m1_subset_1(C_607,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1743,c_1674])).

tff(c_1766,plain,(
    ! [C_607] :
      ( ~ v3_yellow_6('#skF_4'('#skF_8','#skF_9',C_607),'#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9',C_607)
      | ~ m1_subset_1(C_607,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1658,c_1655,c_1660,c_1759])).

tff(c_1768,plain,(
    ! [C_608] :
      ( ~ v3_yellow_6('#skF_4'('#skF_8','#skF_9',C_608),'#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9',C_608)
      | ~ m1_subset_1(C_608,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_1766])).

tff(c_1771,plain,(
    ! [C_608] :
      ( ~ r3_waybel_9('#skF_8','#skF_9',C_608)
      | ~ m1_subset_1(C_608,u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9',C_608)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9',C_608),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9',C_608))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9',C_608))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9',C_608))
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_1768])).

tff(c_1774,plain,(
    ! [C_608] :
      ( ~ r3_waybel_9('#skF_8','#skF_9',C_608)
      | ~ m1_subset_1(C_608,u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9',C_608)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9',C_608),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9',C_608))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9',C_608))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9',C_608))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1771])).

tff(c_1798,plain,(
    ! [C_622] :
      ( ~ r3_waybel_9('#skF_8','#skF_9',C_622)
      | ~ m1_subset_1(C_622,u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9',C_622)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9',C_622),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9',C_622))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9',C_622))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9',C_622)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1774])).

tff(c_1806,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_1798])).

tff(c_1813,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_1806])).

tff(c_1814,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1813])).

tff(c_1917,plain,(
    ! [B_682] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_682))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_682,'#skF_8')
      | ~ v7_waybel_0(B_682)
      | ~ v4_orders_2(B_682)
      | v2_struct_0(B_682)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1913,c_1814])).

tff(c_1920,plain,(
    ! [B_682] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_682))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_682,'#skF_8')
      | ~ v7_waybel_0(B_682)
      | ~ v4_orders_2(B_682)
      | v2_struct_0(B_682)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_1658,c_1655,c_1660,c_1917])).

tff(c_1921,plain,(
    ! [B_682] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_682)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_682))
      | ~ l1_waybel_0(B_682,'#skF_8')
      | ~ v7_waybel_0(B_682)
      | ~ v4_orders_2(B_682)
      | v2_struct_0(B_682) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_1920])).

tff(c_1958,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1921])).

tff(c_1962,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_1958])).

tff(c_1966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1962])).

tff(c_1968,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1921])).

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

tff(c_1790,plain,(
    ! [A_616,B_617,C_618] :
      ( v4_orders_2('#skF_4'(A_616,B_617,C_618))
      | ~ l1_struct_0(A_616)
      | ~ r3_waybel_9(A_616,B_617,C_618)
      | ~ m1_subset_1(C_618,u1_struct_0(A_616))
      | ~ l1_waybel_0(B_617,A_616)
      | ~ v7_waybel_0(B_617)
      | ~ v4_orders_2(B_617)
      | v2_struct_0(B_617)
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616) ) ),
    inference(resolution,[status(thm)],[c_1743,c_40])).

tff(c_1796,plain,(
    ! [A_139,B_617,B_143] :
      ( v4_orders_2('#skF_4'(A_139,B_617,'#skF_5'(A_139,B_143)))
      | ~ l1_struct_0(A_139)
      | ~ r3_waybel_9(A_139,B_617,'#skF_5'(A_139,B_143))
      | ~ l1_waybel_0(B_617,A_139)
      | ~ v7_waybel_0(B_617)
      | ~ v4_orders_2(B_617)
      | v2_struct_0(B_617)
      | ~ l1_waybel_0(B_143,A_139)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_58,c_1790])).

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

tff(c_1783,plain,(
    ! [A_613,B_614,C_615] :
      ( v7_waybel_0('#skF_4'(A_613,B_614,C_615))
      | ~ l1_struct_0(A_613)
      | ~ r3_waybel_9(A_613,B_614,C_615)
      | ~ m1_subset_1(C_615,u1_struct_0(A_613))
      | ~ l1_waybel_0(B_614,A_613)
      | ~ v7_waybel_0(B_614)
      | ~ v4_orders_2(B_614)
      | v2_struct_0(B_614)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_1743,c_38])).

tff(c_1789,plain,(
    ! [A_139,B_614,B_143] :
      ( v7_waybel_0('#skF_4'(A_139,B_614,'#skF_5'(A_139,B_143)))
      | ~ l1_struct_0(A_139)
      | ~ r3_waybel_9(A_139,B_614,'#skF_5'(A_139,B_143))
      | ~ l1_waybel_0(B_614,A_139)
      | ~ v7_waybel_0(B_614)
      | ~ v4_orders_2(B_614)
      | v2_struct_0(B_614)
      | ~ l1_waybel_0(B_143,A_139)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_58,c_1783])).

tff(c_1969,plain,(
    ! [B_705] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_705))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_705)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_705)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_705)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_705))
      | ~ l1_waybel_0(B_705,'#skF_8')
      | ~ v7_waybel_0(B_705)
      | ~ v4_orders_2(B_705)
      | v2_struct_0(B_705) ) ),
    inference(splitRight,[status(thm)],[c_1921])).

tff(c_1973,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1789,c_1969])).

tff(c_1976,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_1658,c_1655,c_1660,c_1968,c_1973])).

tff(c_1978,plain,(
    ! [B_706] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_706))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_706)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_706)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_706))
      | ~ l1_waybel_0(B_706,'#skF_8')
      | ~ v7_waybel_0(B_706)
      | ~ v4_orders_2(B_706)
      | v2_struct_0(B_706) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_1976])).

tff(c_1982,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1796,c_1978])).

tff(c_1985,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_1658,c_1655,c_1660,c_1968,c_1982])).

tff(c_1987,plain,(
    ! [B_707] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_707))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_707)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_707))
      | ~ l1_waybel_0(B_707,'#skF_8')
      | ~ v7_waybel_0(B_707)
      | ~ v4_orders_2(B_707)
      | v2_struct_0(B_707) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_1985])).

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

tff(c_1762,plain,(
    ! [A_605,B_606,C_607] :
      ( ~ v2_struct_0('#skF_4'(A_605,B_606,C_607))
      | ~ l1_struct_0(A_605)
      | ~ r3_waybel_9(A_605,B_606,C_607)
      | ~ m1_subset_1(C_607,u1_struct_0(A_605))
      | ~ l1_waybel_0(B_606,A_605)
      | ~ v7_waybel_0(B_606)
      | ~ v4_orders_2(B_606)
      | v2_struct_0(B_606)
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_1743,c_42])).

tff(c_1989,plain,(
    ! [B_707] :
      ( ~ l1_struct_0('#skF_8')
      | ~ m1_subset_1('#skF_5'('#skF_8',B_707),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_707))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_707))
      | ~ l1_waybel_0(B_707,'#skF_8')
      | ~ v7_waybel_0(B_707)
      | ~ v4_orders_2(B_707)
      | v2_struct_0(B_707) ) ),
    inference(resolution,[status(thm)],[c_1987,c_1762])).

tff(c_1992,plain,(
    ! [B_707] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_707),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_707))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_707))
      | ~ l1_waybel_0(B_707,'#skF_8')
      | ~ v7_waybel_0(B_707)
      | ~ v4_orders_2(B_707)
      | v2_struct_0(B_707) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1658,c_1655,c_1660,c_1968,c_1989])).

tff(c_1999,plain,(
    ! [B_712] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_712),u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_712))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_712))
      | ~ l1_waybel_0(B_712,'#skF_8')
      | ~ v7_waybel_0(B_712)
      | ~ v4_orders_2(B_712)
      | v2_struct_0(B_712) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_1992])).

tff(c_2003,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_1999])).

tff(c_2006,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_2003])).

tff(c_2008,plain,(
    ! [B_713] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_713))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_713))
      | ~ l1_waybel_0(B_713,'#skF_8')
      | ~ v7_waybel_0(B_713)
      | ~ v4_orders_2(B_713)
      | v2_struct_0(B_713) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2006])).

tff(c_1830,plain,(
    ! [C_626,A_627,B_628] :
      ( r2_hidden(C_626,k10_yellow_6(A_627,'#skF_4'(A_627,B_628,C_626)))
      | ~ r3_waybel_9(A_627,B_628,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0(A_627))
      | ~ l1_waybel_0(B_628,A_627)
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1845,plain,(
    ! [A_627,B_628,C_626] :
      ( ~ r1_tarski(k10_yellow_6(A_627,'#skF_4'(A_627,B_628,C_626)),C_626)
      | ~ r3_waybel_9(A_627,B_628,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0(A_627))
      | ~ l1_waybel_0(B_628,A_627)
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(resolution,[status(thm)],[c_1830,c_10])).

tff(c_2024,plain,(
    ! [B_713] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5'('#skF_8',B_713))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_713))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_713),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_713))
      | ~ l1_waybel_0(B_713,'#skF_8')
      | ~ v7_waybel_0(B_713)
      | ~ v4_orders_2(B_713)
      | v2_struct_0(B_713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_1845])).

tff(c_2057,plain,(
    ! [B_713] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_713),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_713))
      | ~ l1_waybel_0(B_713,'#skF_8')
      | ~ v7_waybel_0(B_713)
      | ~ v4_orders_2(B_713)
      | v2_struct_0(B_713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1658,c_1655,c_1660,c_1666,c_2024])).

tff(c_2075,plain,(
    ! [B_714] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_714),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_714))
      | ~ l1_waybel_0(B_714,'#skF_8')
      | ~ v7_waybel_0(B_714)
      | ~ v4_orders_2(B_714)
      | v2_struct_0(B_714) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_2057])).

tff(c_2079,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_2075])).

tff(c_2082,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_143))
      | ~ l1_waybel_0(B_143,'#skF_8')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_2079])).

tff(c_2084,plain,(
    ! [B_715] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_715))
      | ~ l1_waybel_0(B_715,'#skF_8')
      | ~ v7_waybel_0(B_715)
      | ~ v4_orders_2(B_715)
      | v2_struct_0(B_715) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2082])).

tff(c_2092,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_2084])).

tff(c_2099,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1652,c_1658,c_1655,c_1660,c_2092])).

tff(c_2101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1651,c_2099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:00:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.43/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.45  
% 7.52/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.45  %$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 7.52/2.45  
% 7.52/2.45  %Foreground sorts:
% 7.52/2.45  
% 7.52/2.45  
% 7.52/2.45  %Background operators:
% 7.52/2.45  
% 7.52/2.45  
% 7.52/2.45  %Foreground operators:
% 7.52/2.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.52/2.45  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.52/2.45  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 7.52/2.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.52/2.45  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.52/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.52/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.52/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.52/2.45  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 7.52/2.45  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 7.52/2.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.52/2.45  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 7.52/2.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.52/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.52/2.45  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 7.52/2.45  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 7.52/2.45  tff('#skF_10', type, '#skF_10': $i > $i).
% 7.52/2.45  tff(k6_yellow_6, type, k6_yellow_6: $i > $i).
% 7.52/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.52/2.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.52/2.45  tff('#skF_9', type, '#skF_9': $i).
% 7.52/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.52/2.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.52/2.45  tff('#skF_8', type, '#skF_8': $i).
% 7.52/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.52/2.45  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 7.52/2.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.52/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.52/2.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.52/2.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.52/2.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.52/2.45  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 7.52/2.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.52/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.52/2.45  
% 7.52/2.49  tff(f_301, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 7.52/2.49  tff(f_276, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ~(r2_hidden(B, k6_yellow_6(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r3_waybel_9(A, B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_yellow19)).
% 7.52/2.49  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.52/2.49  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 7.52/2.49  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.52/2.49  tff(f_96, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 7.52/2.49  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 7.52/2.49  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.52/2.49  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 7.52/2.49  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.52/2.49  tff(f_122, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 7.52/2.49  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 7.52/2.49  tff(f_248, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l37_yellow19)).
% 7.52/2.49  tff(f_224, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 7.52/2.49  tff(c_80, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_90, plain, (~v2_struct_0('#skF_9') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_117, plain, (~v1_compts_1('#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 7.52/2.49  tff(c_78, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_76, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_68, plain, (![A_145]: (v4_orders_2('#skF_7'(A_145)) | v1_compts_1(A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_276])).
% 7.52/2.49  tff(c_116, plain, (![B_164]: (v1_compts_1('#skF_8') | m2_yellow_6('#skF_10'(B_164), '#skF_8', B_164) | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_158, plain, (![B_164]: (m2_yellow_6('#skF_10'(B_164), '#skF_8', B_164) | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_117, c_116])).
% 7.52/2.49  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.52/2.49  tff(c_14, plain, (![A_10, B_54, C_76]: (m1_subset_1('#skF_2'(A_10, B_54, C_76), u1_struct_0(A_10)) | k10_yellow_6(A_10, B_54)=C_76 | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.52/2.49  tff(c_121, plain, (![A_170, B_171]: (r1_tarski(A_170, B_171) | ~m1_subset_1(A_170, k1_zfmisc_1(B_171)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.52/2.49  tff(c_125, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_121])).
% 7.52/2.49  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.52/2.49  tff(c_34, plain, (![A_94, B_95]: (m1_subset_1(k10_yellow_6(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_waybel_0(B_95, A_94) | ~v7_waybel_0(B_95) | ~v4_orders_2(B_95) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.52/2.49  tff(c_356, plain, (![A_280, B_281, D_282]: (m1_connsp_2('#skF_1'(A_280, B_281, k10_yellow_6(A_280, B_281), D_282), A_280, D_282) | r2_hidden(D_282, k10_yellow_6(A_280, B_281)) | ~m1_subset_1(D_282, u1_struct_0(A_280)) | ~m1_subset_1(k10_yellow_6(A_280, B_281), k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_waybel_0(B_281, A_280) | ~v7_waybel_0(B_281) | ~v4_orders_2(B_281) | v2_struct_0(B_281) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.52/2.49  tff(c_362, plain, (![A_94, B_95, D_282]: (m1_connsp_2('#skF_1'(A_94, B_95, k10_yellow_6(A_94, B_95), D_282), A_94, D_282) | r2_hidden(D_282, k10_yellow_6(A_94, B_95)) | ~m1_subset_1(D_282, u1_struct_0(A_94)) | ~l1_waybel_0(B_95, A_94) | ~v7_waybel_0(B_95) | ~v4_orders_2(B_95) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_34, c_356])).
% 7.52/2.49  tff(c_368, plain, (![A_286, B_287, C_288, E_289]: (r2_hidden('#skF_2'(A_286, B_287, C_288), C_288) | r1_waybel_0(A_286, B_287, E_289) | ~m1_connsp_2(E_289, A_286, '#skF_2'(A_286, B_287, C_288)) | k10_yellow_6(A_286, B_287)=C_288 | ~m1_subset_1(C_288, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_waybel_0(B_287, A_286) | ~v7_waybel_0(B_287) | ~v4_orders_2(B_287) | v2_struct_0(B_287) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.52/2.49  tff(c_520, plain, (![A_413, B_414, C_415, B_416]: (r2_hidden('#skF_2'(A_413, B_414, C_415), C_415) | r1_waybel_0(A_413, B_414, '#skF_1'(A_413, B_416, k10_yellow_6(A_413, B_416), '#skF_2'(A_413, B_414, C_415))) | k10_yellow_6(A_413, B_414)=C_415 | ~m1_subset_1(C_415, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_waybel_0(B_414, A_413) | ~v7_waybel_0(B_414) | ~v4_orders_2(B_414) | v2_struct_0(B_414) | r2_hidden('#skF_2'(A_413, B_414, C_415), k10_yellow_6(A_413, B_416)) | ~m1_subset_1('#skF_2'(A_413, B_414, C_415), u1_struct_0(A_413)) | ~l1_waybel_0(B_416, A_413) | ~v7_waybel_0(B_416) | ~v4_orders_2(B_416) | v2_struct_0(B_416) | ~l1_pre_topc(A_413) | ~v2_pre_topc(A_413) | v2_struct_0(A_413))), inference(resolution, [status(thm)], [c_362, c_368])).
% 7.52/2.49  tff(c_30, plain, (![A_10, B_54, D_87]: (~r1_waybel_0(A_10, B_54, '#skF_1'(A_10, B_54, k10_yellow_6(A_10, B_54), D_87)) | r2_hidden(D_87, k10_yellow_6(A_10, B_54)) | ~m1_subset_1(D_87, u1_struct_0(A_10)) | ~m1_subset_1(k10_yellow_6(A_10, B_54), k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.52/2.49  tff(c_547, plain, (![A_417, B_418, C_419]: (~m1_subset_1(k10_yellow_6(A_417, B_418), k1_zfmisc_1(u1_struct_0(A_417))) | r2_hidden('#skF_2'(A_417, B_418, C_419), C_419) | k10_yellow_6(A_417, B_418)=C_419 | ~m1_subset_1(C_419, k1_zfmisc_1(u1_struct_0(A_417))) | r2_hidden('#skF_2'(A_417, B_418, C_419), k10_yellow_6(A_417, B_418)) | ~m1_subset_1('#skF_2'(A_417, B_418, C_419), u1_struct_0(A_417)) | ~l1_waybel_0(B_418, A_417) | ~v7_waybel_0(B_418) | ~v4_orders_2(B_418) | v2_struct_0(B_418) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(resolution, [status(thm)], [c_520, c_30])).
% 7.52/2.49  tff(c_571, plain, (![A_420, B_421, C_422]: (r2_hidden('#skF_2'(A_420, B_421, C_422), C_422) | k10_yellow_6(A_420, B_421)=C_422 | ~m1_subset_1(C_422, k1_zfmisc_1(u1_struct_0(A_420))) | r2_hidden('#skF_2'(A_420, B_421, C_422), k10_yellow_6(A_420, B_421)) | ~m1_subset_1('#skF_2'(A_420, B_421, C_422), u1_struct_0(A_420)) | ~l1_waybel_0(B_421, A_420) | ~v7_waybel_0(B_421) | ~v4_orders_2(B_421) | v2_struct_0(B_421) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | v2_struct_0(A_420))), inference(resolution, [status(thm)], [c_34, c_547])).
% 7.52/2.49  tff(c_48, plain, (![A_103, B_107, C_109]: (r3_waybel_9(A_103, B_107, C_109) | ~r2_hidden(C_109, k10_yellow_6(A_103, B_107)) | ~m1_subset_1(C_109, u1_struct_0(A_103)) | ~l1_waybel_0(B_107, A_103) | ~v7_waybel_0(B_107) | ~v4_orders_2(B_107) | v2_struct_0(B_107) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.52/2.49  tff(c_612, plain, (![A_423, B_424, C_425]: (r3_waybel_9(A_423, B_424, '#skF_2'(A_423, B_424, C_425)) | r2_hidden('#skF_2'(A_423, B_424, C_425), C_425) | k10_yellow_6(A_423, B_424)=C_425 | ~m1_subset_1(C_425, k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_subset_1('#skF_2'(A_423, B_424, C_425), u1_struct_0(A_423)) | ~l1_waybel_0(B_424, A_423) | ~v7_waybel_0(B_424) | ~v4_orders_2(B_424) | v2_struct_0(B_424) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(resolution, [status(thm)], [c_571, c_48])).
% 7.52/2.49  tff(c_616, plain, (![A_426, B_427, C_428]: (r3_waybel_9(A_426, B_427, '#skF_2'(A_426, B_427, C_428)) | r2_hidden('#skF_2'(A_426, B_427, C_428), C_428) | k10_yellow_6(A_426, B_427)=C_428 | ~m1_subset_1(C_428, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_waybel_0(B_427, A_426) | ~v7_waybel_0(B_427) | ~v4_orders_2(B_427) | v2_struct_0(B_427) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(resolution, [status(thm)], [c_14, c_612])).
% 7.52/2.49  tff(c_651, plain, (![A_435, B_436, A_437]: (r3_waybel_9(A_435, B_436, '#skF_2'(A_435, B_436, A_437)) | r2_hidden('#skF_2'(A_435, B_436, A_437), A_437) | k10_yellow_6(A_435, B_436)=A_437 | ~l1_waybel_0(B_436, A_435) | ~v7_waybel_0(B_436) | ~v4_orders_2(B_436) | v2_struct_0(B_436) | ~l1_pre_topc(A_435) | ~v2_pre_topc(A_435) | v2_struct_0(A_435) | ~r1_tarski(A_437, u1_struct_0(A_435)))), inference(resolution, [status(thm)], [c_6, c_616])).
% 7.52/2.49  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.52/2.49  tff(c_682, plain, (![A_438, A_439, B_440]: (~r1_tarski(A_438, '#skF_2'(A_439, B_440, A_438)) | r3_waybel_9(A_439, B_440, '#skF_2'(A_439, B_440, A_438)) | k10_yellow_6(A_439, B_440)=A_438 | ~l1_waybel_0(B_440, A_439) | ~v7_waybel_0(B_440) | ~v4_orders_2(B_440) | v2_struct_0(B_440) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439) | ~r1_tarski(A_438, u1_struct_0(A_439)))), inference(resolution, [status(thm)], [c_651, c_10])).
% 7.52/2.49  tff(c_685, plain, (![A_439, B_440]: (r3_waybel_9(A_439, B_440, '#skF_2'(A_439, B_440, k1_xboole_0)) | k10_yellow_6(A_439, B_440)=k1_xboole_0 | ~l1_waybel_0(B_440, A_439) | ~v7_waybel_0(B_440) | ~v4_orders_2(B_440) | v2_struct_0(B_440) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_439)))), inference(resolution, [status(thm)], [c_125, c_682])).
% 7.52/2.49  tff(c_689, plain, (![A_441, B_442]: (r3_waybel_9(A_441, B_442, '#skF_2'(A_441, B_442, k1_xboole_0)) | k10_yellow_6(A_441, B_442)=k1_xboole_0 | ~l1_waybel_0(B_442, A_441) | ~v7_waybel_0(B_442) | ~v4_orders_2(B_442) | v2_struct_0(B_442) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441) | v2_struct_0(A_441))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_685])).
% 7.52/2.49  tff(c_50, plain, (![A_110, B_118, D_124, C_122]: (r3_waybel_9(A_110, B_118, D_124) | ~r3_waybel_9(A_110, C_122, D_124) | ~m1_subset_1(D_124, u1_struct_0(A_110)) | ~m2_yellow_6(C_122, A_110, B_118) | ~l1_waybel_0(B_118, A_110) | ~v7_waybel_0(B_118) | ~v4_orders_2(B_118) | v2_struct_0(B_118) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.52/2.49  tff(c_1168, plain, (![A_510, B_511, B_512]: (r3_waybel_9(A_510, B_511, '#skF_2'(A_510, B_512, k1_xboole_0)) | ~m1_subset_1('#skF_2'(A_510, B_512, k1_xboole_0), u1_struct_0(A_510)) | ~m2_yellow_6(B_512, A_510, B_511) | ~l1_waybel_0(B_511, A_510) | ~v7_waybel_0(B_511) | ~v4_orders_2(B_511) | v2_struct_0(B_511) | k10_yellow_6(A_510, B_512)=k1_xboole_0 | ~l1_waybel_0(B_512, A_510) | ~v7_waybel_0(B_512) | ~v4_orders_2(B_512) | v2_struct_0(B_512) | ~l1_pre_topc(A_510) | ~v2_pre_topc(A_510) | v2_struct_0(A_510))), inference(resolution, [status(thm)], [c_689, c_50])).
% 7.52/2.49  tff(c_1177, plain, (![A_10, B_511, B_54]: (r3_waybel_9(A_10, B_511, '#skF_2'(A_10, B_54, k1_xboole_0)) | ~m2_yellow_6(B_54, A_10, B_511) | ~l1_waybel_0(B_511, A_10) | ~v7_waybel_0(B_511) | ~v4_orders_2(B_511) | v2_struct_0(B_511) | k10_yellow_6(A_10, B_54)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_14, c_1168])).
% 7.52/2.49  tff(c_1187, plain, (![A_513, B_514, B_515]: (r3_waybel_9(A_513, B_514, '#skF_2'(A_513, B_515, k1_xboole_0)) | ~m2_yellow_6(B_515, A_513, B_514) | ~l1_waybel_0(B_514, A_513) | ~v7_waybel_0(B_514) | ~v4_orders_2(B_514) | v2_struct_0(B_514) | k10_yellow_6(A_513, B_515)=k1_xboole_0 | ~l1_waybel_0(B_515, A_513) | ~v7_waybel_0(B_515) | ~v4_orders_2(B_515) | v2_struct_0(B_515) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1177])).
% 7.52/2.49  tff(c_60, plain, (![A_145, C_155]: (~r3_waybel_9(A_145, '#skF_7'(A_145), C_155) | ~m1_subset_1(C_155, u1_struct_0(A_145)) | v1_compts_1(A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_276])).
% 7.52/2.49  tff(c_1214, plain, (![A_519, B_520]: (~m1_subset_1('#skF_2'(A_519, B_520, k1_xboole_0), u1_struct_0(A_519)) | v1_compts_1(A_519) | ~m2_yellow_6(B_520, A_519, '#skF_7'(A_519)) | ~l1_waybel_0('#skF_7'(A_519), A_519) | ~v7_waybel_0('#skF_7'(A_519)) | ~v4_orders_2('#skF_7'(A_519)) | v2_struct_0('#skF_7'(A_519)) | k10_yellow_6(A_519, B_520)=k1_xboole_0 | ~l1_waybel_0(B_520, A_519) | ~v7_waybel_0(B_520) | ~v4_orders_2(B_520) | v2_struct_0(B_520) | ~l1_pre_topc(A_519) | ~v2_pre_topc(A_519) | v2_struct_0(A_519))), inference(resolution, [status(thm)], [c_1187, c_60])).
% 7.52/2.49  tff(c_1226, plain, (![A_10, B_54]: (v1_compts_1(A_10) | ~m2_yellow_6(B_54, A_10, '#skF_7'(A_10)) | ~l1_waybel_0('#skF_7'(A_10), A_10) | ~v7_waybel_0('#skF_7'(A_10)) | ~v4_orders_2('#skF_7'(A_10)) | v2_struct_0('#skF_7'(A_10)) | k10_yellow_6(A_10, B_54)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_14, c_1214])).
% 7.52/2.49  tff(c_1288, plain, (![A_526, B_527]: (v1_compts_1(A_526) | ~m2_yellow_6(B_527, A_526, '#skF_7'(A_526)) | ~l1_waybel_0('#skF_7'(A_526), A_526) | ~v7_waybel_0('#skF_7'(A_526)) | ~v4_orders_2('#skF_7'(A_526)) | v2_struct_0('#skF_7'(A_526)) | k10_yellow_6(A_526, B_527)=k1_xboole_0 | ~l1_waybel_0(B_527, A_526) | ~v7_waybel_0(B_527) | ~v4_orders_2(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_526) | ~v2_pre_topc(A_526) | v2_struct_0(A_526))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1226])).
% 7.52/2.49  tff(c_1296, plain, (v1_compts_1('#skF_8') | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_158, c_1288])).
% 7.52/2.49  tff(c_1300, plain, (v1_compts_1('#skF_8') | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1296])).
% 7.52/2.49  tff(c_1301, plain, (k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1300])).
% 7.52/2.49  tff(c_1302, plain, (~v4_orders_2('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_1301])).
% 7.52/2.49  tff(c_1305, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_68, c_1302])).
% 7.52/2.49  tff(c_1308, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1305])).
% 7.52/2.49  tff(c_1310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1308])).
% 7.52/2.49  tff(c_1312, plain, (v4_orders_2('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1301])).
% 7.52/2.49  tff(c_66, plain, (![A_145]: (v7_waybel_0('#skF_7'(A_145)) | v1_compts_1(A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_276])).
% 7.52/2.49  tff(c_64, plain, (![A_145]: (l1_waybel_0('#skF_7'(A_145), A_145) | v1_compts_1(A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_276])).
% 7.52/2.49  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.52/2.49  tff(c_162, plain, (![C_195, A_196, B_197]: (~v2_struct_0(C_195) | ~m2_yellow_6(C_195, A_196, B_197) | ~l1_waybel_0(B_197, A_196) | ~v7_waybel_0(B_197) | ~v4_orders_2(B_197) | v2_struct_0(B_197) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_165, plain, (![B_164]: (~v2_struct_0('#skF_10'(B_164)) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(resolution, [status(thm)], [c_158, c_162])).
% 7.52/2.49  tff(c_168, plain, (![B_164]: (~v2_struct_0('#skF_10'(B_164)) | ~l1_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_80, c_165])).
% 7.52/2.49  tff(c_169, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_168])).
% 7.52/2.49  tff(c_172, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_12, c_169])).
% 7.52/2.49  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_172])).
% 7.52/2.49  tff(c_178, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_168])).
% 7.52/2.49  tff(c_198, plain, (![C_207, A_208, B_209]: (l1_waybel_0(C_207, A_208) | ~m2_yellow_6(C_207, A_208, B_209) | ~l1_waybel_0(B_209, A_208) | ~v7_waybel_0(B_209) | ~v4_orders_2(B_209) | v2_struct_0(B_209) | ~l1_struct_0(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_201, plain, (![B_164]: (l1_waybel_0('#skF_10'(B_164), '#skF_8') | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(resolution, [status(thm)], [c_158, c_198])).
% 7.52/2.49  tff(c_204, plain, (![B_164]: (l1_waybel_0('#skF_10'(B_164), '#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_201])).
% 7.52/2.49  tff(c_205, plain, (![B_164]: (l1_waybel_0('#skF_10'(B_164), '#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_80, c_204])).
% 7.52/2.49  tff(c_1311, plain, (~v7_waybel_0('#skF_7'('#skF_8')) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | v2_struct_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1301])).
% 7.52/2.49  tff(c_1313, plain, (~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8')), inference(splitLeft, [status(thm)], [c_1311])).
% 7.52/2.49  tff(c_1316, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_205, c_1313])).
% 7.52/2.49  tff(c_1319, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1316])).
% 7.52/2.49  tff(c_1320, plain, (~v7_waybel_0('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_1319])).
% 7.52/2.49  tff(c_1323, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_66, c_1320])).
% 7.52/2.49  tff(c_1326, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1323])).
% 7.52/2.49  tff(c_1328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1326])).
% 7.52/2.49  tff(c_1329, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1319])).
% 7.52/2.49  tff(c_1362, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1329])).
% 7.52/2.49  tff(c_1365, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_1362])).
% 7.52/2.49  tff(c_1368, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1365])).
% 7.52/2.49  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1368])).
% 7.52/2.49  tff(c_1371, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1329])).
% 7.52/2.49  tff(c_70, plain, (![A_145]: (~v2_struct_0('#skF_7'(A_145)) | v1_compts_1(A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_276])).
% 7.52/2.49  tff(c_1375, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1371, c_70])).
% 7.52/2.49  tff(c_1378, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1375])).
% 7.52/2.49  tff(c_1380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1378])).
% 7.52/2.49  tff(c_1381, plain, (~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1311])).
% 7.52/2.49  tff(c_1383, plain, (~v7_waybel_0('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_1381])).
% 7.52/2.49  tff(c_1386, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_66, c_1383])).
% 7.52/2.49  tff(c_1389, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1386])).
% 7.52/2.49  tff(c_1391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1389])).
% 7.52/2.49  tff(c_1393, plain, (v7_waybel_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1381])).
% 7.52/2.49  tff(c_188, plain, (![C_202, A_203, B_204]: (v7_waybel_0(C_202) | ~m2_yellow_6(C_202, A_203, B_204) | ~l1_waybel_0(B_204, A_203) | ~v7_waybel_0(B_204) | ~v4_orders_2(B_204) | v2_struct_0(B_204) | ~l1_struct_0(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_191, plain, (![B_164]: (v7_waybel_0('#skF_10'(B_164)) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(resolution, [status(thm)], [c_158, c_188])).
% 7.52/2.49  tff(c_194, plain, (![B_164]: (v7_waybel_0('#skF_10'(B_164)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_191])).
% 7.52/2.49  tff(c_195, plain, (![B_164]: (v7_waybel_0('#skF_10'(B_164)) | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_80, c_194])).
% 7.52/2.49  tff(c_1392, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1381])).
% 7.52/2.49  tff(c_1394, plain, (~v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))), inference(splitLeft, [status(thm)], [c_1392])).
% 7.52/2.49  tff(c_1397, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_195, c_1394])).
% 7.52/2.49  tff(c_1400, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1393, c_1397])).
% 7.52/2.49  tff(c_1432, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1400])).
% 7.52/2.49  tff(c_1435, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_1432])).
% 7.52/2.49  tff(c_1438, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1435])).
% 7.52/2.49  tff(c_1440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1438])).
% 7.52/2.49  tff(c_1441, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1400])).
% 7.52/2.49  tff(c_1445, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1441, c_70])).
% 7.52/2.49  tff(c_1448, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1445])).
% 7.52/2.49  tff(c_1450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1448])).
% 7.52/2.49  tff(c_1451, plain, (~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1392])).
% 7.52/2.49  tff(c_1453, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1451])).
% 7.52/2.49  tff(c_1456, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_1453])).
% 7.52/2.49  tff(c_1459, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1456])).
% 7.52/2.49  tff(c_1461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1459])).
% 7.52/2.49  tff(c_1463, plain, (l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_1451])).
% 7.52/2.49  tff(c_180, plain, (![C_199, A_200, B_201]: (v4_orders_2(C_199) | ~m2_yellow_6(C_199, A_200, B_201) | ~l1_waybel_0(B_201, A_200) | ~v7_waybel_0(B_201) | ~v4_orders_2(B_201) | v2_struct_0(B_201) | ~l1_struct_0(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_183, plain, (![B_164]: (v4_orders_2('#skF_10'(B_164)) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(resolution, [status(thm)], [c_158, c_180])).
% 7.52/2.49  tff(c_186, plain, (![B_164]: (v4_orders_2('#skF_10'(B_164)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_183])).
% 7.52/2.49  tff(c_187, plain, (![B_164]: (v4_orders_2('#skF_10'(B_164)) | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_80, c_186])).
% 7.52/2.49  tff(c_1462, plain, (~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1451])).
% 7.52/2.49  tff(c_1464, plain, (~v4_orders_2('#skF_10'('#skF_7'('#skF_8')))), inference(splitLeft, [status(thm)], [c_1462])).
% 7.52/2.49  tff(c_1467, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_187, c_1464])).
% 7.52/2.49  tff(c_1470, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1393, c_1463, c_1467])).
% 7.52/2.49  tff(c_1504, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1470, c_70])).
% 7.52/2.49  tff(c_1507, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1504])).
% 7.52/2.49  tff(c_1509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1507])).
% 7.52/2.49  tff(c_1510, plain, (k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1462])).
% 7.52/2.49  tff(c_1512, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_1510])).
% 7.52/2.49  tff(c_1515, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1512, c_70])).
% 7.52/2.49  tff(c_1518, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1515])).
% 7.52/2.49  tff(c_1520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_117, c_1518])).
% 7.52/2.49  tff(c_1522, plain, (~v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_1510])).
% 7.52/2.49  tff(c_1521, plain, (v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1510])).
% 7.52/2.49  tff(c_1523, plain, (k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1521])).
% 7.52/2.49  tff(c_104, plain, (![B_164]: (v1_compts_1('#skF_8') | v3_yellow_6('#skF_10'(B_164), '#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_154, plain, (![B_164]: (v3_yellow_6('#skF_10'(B_164), '#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(negUnitSimplification, [status(thm)], [c_117, c_104])).
% 7.52/2.49  tff(c_216, plain, (![A_215, B_216]: (k10_yellow_6(A_215, B_216)!=k1_xboole_0 | ~v3_yellow_6(B_216, A_215) | ~l1_waybel_0(B_216, A_215) | ~v7_waybel_0(B_216) | ~v4_orders_2(B_216) | v2_struct_0(B_216) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.52/2.49  tff(c_219, plain, (![B_164]: (k10_yellow_6('#skF_8', '#skF_10'(B_164))!=k1_xboole_0 | ~l1_waybel_0('#skF_10'(B_164), '#skF_8') | ~v7_waybel_0('#skF_10'(B_164)) | ~v4_orders_2('#skF_10'(B_164)) | v2_struct_0('#skF_10'(B_164)) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(resolution, [status(thm)], [c_154, c_216])).
% 7.52/2.49  tff(c_222, plain, (![B_164]: (k10_yellow_6('#skF_8', '#skF_10'(B_164))!=k1_xboole_0 | ~l1_waybel_0('#skF_10'(B_164), '#skF_8') | ~v7_waybel_0('#skF_10'(B_164)) | ~v4_orders_2('#skF_10'(B_164)) | v2_struct_0('#skF_10'(B_164)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_219])).
% 7.52/2.49  tff(c_243, plain, (![B_228]: (k10_yellow_6('#skF_8', '#skF_10'(B_228))!=k1_xboole_0 | ~l1_waybel_0('#skF_10'(B_228), '#skF_8') | ~v7_waybel_0('#skF_10'(B_228)) | ~v4_orders_2('#skF_10'(B_228)) | v2_struct_0('#skF_10'(B_228)) | ~l1_waybel_0(B_228, '#skF_8') | ~v7_waybel_0(B_228) | ~v4_orders_2(B_228) | v2_struct_0(B_228))), inference(negUnitSimplification, [status(thm)], [c_80, c_222])).
% 7.52/2.49  tff(c_248, plain, (![B_229]: (k10_yellow_6('#skF_8', '#skF_10'(B_229))!=k1_xboole_0 | ~v7_waybel_0('#skF_10'(B_229)) | ~v4_orders_2('#skF_10'(B_229)) | v2_struct_0('#skF_10'(B_229)) | ~l1_waybel_0(B_229, '#skF_8') | ~v7_waybel_0(B_229) | ~v4_orders_2(B_229) | v2_struct_0(B_229))), inference(resolution, [status(thm)], [c_205, c_243])).
% 7.52/2.49  tff(c_253, plain, (![B_230]: (k10_yellow_6('#skF_8', '#skF_10'(B_230))!=k1_xboole_0 | ~v4_orders_2('#skF_10'(B_230)) | v2_struct_0('#skF_10'(B_230)) | ~l1_waybel_0(B_230, '#skF_8') | ~v7_waybel_0(B_230) | ~v4_orders_2(B_230) | v2_struct_0(B_230))), inference(resolution, [status(thm)], [c_195, c_248])).
% 7.52/2.49  tff(c_258, plain, (![B_231]: (k10_yellow_6('#skF_8', '#skF_10'(B_231))!=k1_xboole_0 | v2_struct_0('#skF_10'(B_231)) | ~l1_waybel_0(B_231, '#skF_8') | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231))), inference(resolution, [status(thm)], [c_187, c_253])).
% 7.52/2.49  tff(c_177, plain, (![B_164]: (~v2_struct_0('#skF_10'(B_164)) | ~l1_waybel_0(B_164, '#skF_8') | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164))), inference(splitRight, [status(thm)], [c_168])).
% 7.52/2.49  tff(c_262, plain, (![B_231]: (k10_yellow_6('#skF_8', '#skF_10'(B_231))!=k1_xboole_0 | ~l1_waybel_0(B_231, '#skF_8') | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231))), inference(resolution, [status(thm)], [c_258, c_177])).
% 7.52/2.49  tff(c_1573, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1523, c_262])).
% 7.52/2.49  tff(c_1638, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1393, c_1463, c_1573])).
% 7.52/2.49  tff(c_1640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1522, c_1638])).
% 7.52/2.49  tff(c_1641, plain, (v2_struct_0('#skF_10'('#skF_7'('#skF_8')))), inference(splitRight, [status(thm)], [c_1521])).
% 7.52/2.49  tff(c_1645, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_1641, c_177])).
% 7.52/2.49  tff(c_1648, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1393, c_1463, c_1645])).
% 7.52/2.49  tff(c_1650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1522, c_1648])).
% 7.52/2.49  tff(c_1651, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_90])).
% 7.52/2.49  tff(c_1652, plain, (v1_compts_1('#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 7.52/2.49  tff(c_88, plain, (v4_orders_2('#skF_9') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_1658, plain, (v4_orders_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_88])).
% 7.52/2.49  tff(c_86, plain, (v7_waybel_0('#skF_9') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_1655, plain, (v7_waybel_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_86])).
% 7.52/2.49  tff(c_84, plain, (l1_waybel_0('#skF_9', '#skF_8') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_1660, plain, (l1_waybel_0('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_84])).
% 7.52/2.49  tff(c_56, plain, (![A_139, B_143]: (r3_waybel_9(A_139, B_143, '#skF_5'(A_139, B_143)) | ~l1_waybel_0(B_143, A_139) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.52/2.49  tff(c_58, plain, (![A_139, B_143]: (m1_subset_1('#skF_5'(A_139, B_143), u1_struct_0(A_139)) | ~l1_waybel_0(B_143, A_139) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.52/2.49  tff(c_1662, plain, (![A_547, B_548]: (r1_tarski(A_547, B_548) | ~m1_subset_1(A_547, k1_zfmisc_1(B_548)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.52/2.49  tff(c_1666, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_1662])).
% 7.52/2.49  tff(c_1743, plain, (![A_605, B_606, C_607]: (m2_yellow_6('#skF_4'(A_605, B_606, C_607), A_605, B_606) | ~r3_waybel_9(A_605, B_606, C_607) | ~m1_subset_1(C_607, u1_struct_0(A_605)) | ~l1_waybel_0(B_606, A_605) | ~v7_waybel_0(B_606) | ~v4_orders_2(B_606) | v2_struct_0(B_606) | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(cnfTransformation, [status(thm)], [f_224])).
% 7.52/2.49  tff(c_36, plain, (![C_99, A_96, B_97]: (l1_waybel_0(C_99, A_96) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_1846, plain, (![A_629, B_630, C_631]: (l1_waybel_0('#skF_4'(A_629, B_630, C_631), A_629) | ~l1_struct_0(A_629) | ~r3_waybel_9(A_629, B_630, C_631) | ~m1_subset_1(C_631, u1_struct_0(A_629)) | ~l1_waybel_0(B_630, A_629) | ~v7_waybel_0(B_630) | ~v4_orders_2(B_630) | v2_struct_0(B_630) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(resolution, [status(thm)], [c_1743, c_36])).
% 7.52/2.49  tff(c_1913, plain, (![A_680, B_681, B_682]: (l1_waybel_0('#skF_4'(A_680, B_681, '#skF_5'(A_680, B_682)), A_680) | ~l1_struct_0(A_680) | ~r3_waybel_9(A_680, B_681, '#skF_5'(A_680, B_682)) | ~l1_waybel_0(B_681, A_680) | ~v7_waybel_0(B_681) | ~v4_orders_2(B_681) | v2_struct_0(B_681) | ~l1_waybel_0(B_682, A_680) | ~v7_waybel_0(B_682) | ~v4_orders_2(B_682) | v2_struct_0(B_682) | ~v1_compts_1(A_680) | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(resolution, [status(thm)], [c_58, c_1846])).
% 7.52/2.49  tff(c_44, plain, (![B_102, A_100]: (v3_yellow_6(B_102, A_100) | k10_yellow_6(A_100, B_102)=k1_xboole_0 | ~l1_waybel_0(B_102, A_100) | ~v7_waybel_0(B_102) | ~v4_orders_2(B_102) | v2_struct_0(B_102) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.52/2.49  tff(c_82, plain, (![C_163]: (~v3_yellow_6(C_163, '#skF_8') | ~m2_yellow_6(C_163, '#skF_8', '#skF_9') | ~v1_compts_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_301])).
% 7.52/2.49  tff(c_1674, plain, (![C_163]: (~v3_yellow_6(C_163, '#skF_8') | ~m2_yellow_6(C_163, '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_82])).
% 7.52/2.49  tff(c_1759, plain, (![C_607]: (~v3_yellow_6('#skF_4'('#skF_8', '#skF_9', C_607), '#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', C_607) | ~m1_subset_1(C_607, u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1743, c_1674])).
% 7.52/2.49  tff(c_1766, plain, (![C_607]: (~v3_yellow_6('#skF_4'('#skF_8', '#skF_9', C_607), '#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', C_607) | ~m1_subset_1(C_607, u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1658, c_1655, c_1660, c_1759])).
% 7.52/2.49  tff(c_1768, plain, (![C_608]: (~v3_yellow_6('#skF_4'('#skF_8', '#skF_9', C_608), '#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', C_608) | ~m1_subset_1(C_608, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_1766])).
% 7.52/2.49  tff(c_1771, plain, (![C_608]: (~r3_waybel_9('#skF_8', '#skF_9', C_608) | ~m1_subset_1(C_608, u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', C_608))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', C_608), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', C_608)) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', C_608)) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', C_608)) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_1768])).
% 7.52/2.49  tff(c_1774, plain, (![C_608]: (~r3_waybel_9('#skF_8', '#skF_9', C_608) | ~m1_subset_1(C_608, u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', C_608))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', C_608), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', C_608)) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', C_608)) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', C_608)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1771])).
% 7.52/2.49  tff(c_1798, plain, (![C_622]: (~r3_waybel_9('#skF_8', '#skF_9', C_622) | ~m1_subset_1(C_622, u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', C_622))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', C_622), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', C_622)) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', C_622)) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', C_622)))), inference(negUnitSimplification, [status(thm)], [c_80, c_1774])).
% 7.52/2.49  tff(c_1806, plain, (![B_143]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_1798])).
% 7.52/2.49  tff(c_1813, plain, (![B_143]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_1806])).
% 7.52/2.49  tff(c_1814, plain, (![B_143]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143))), inference(negUnitSimplification, [status(thm)], [c_80, c_1813])).
% 7.52/2.49  tff(c_1917, plain, (![B_682]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682)) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_682, '#skF_8') | ~v7_waybel_0(B_682) | ~v4_orders_2(B_682) | v2_struct_0(B_682) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1913, c_1814])).
% 7.52/2.49  tff(c_1920, plain, (![B_682]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_682, '#skF_8') | ~v7_waybel_0(B_682) | ~v4_orders_2(B_682) | v2_struct_0(B_682) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_1658, c_1655, c_1660, c_1917])).
% 7.52/2.49  tff(c_1921, plain, (![B_682]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_682)) | ~l1_waybel_0(B_682, '#skF_8') | ~v7_waybel_0(B_682) | ~v4_orders_2(B_682) | v2_struct_0(B_682))), inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_1920])).
% 7.52/2.49  tff(c_1958, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1921])).
% 7.52/2.49  tff(c_1962, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_12, c_1958])).
% 7.52/2.49  tff(c_1966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1962])).
% 7.52/2.49  tff(c_1968, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1921])).
% 7.52/2.49  tff(c_40, plain, (![C_99, A_96, B_97]: (v4_orders_2(C_99) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_1790, plain, (![A_616, B_617, C_618]: (v4_orders_2('#skF_4'(A_616, B_617, C_618)) | ~l1_struct_0(A_616) | ~r3_waybel_9(A_616, B_617, C_618) | ~m1_subset_1(C_618, u1_struct_0(A_616)) | ~l1_waybel_0(B_617, A_616) | ~v7_waybel_0(B_617) | ~v4_orders_2(B_617) | v2_struct_0(B_617) | ~l1_pre_topc(A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616))), inference(resolution, [status(thm)], [c_1743, c_40])).
% 7.52/2.49  tff(c_1796, plain, (![A_139, B_617, B_143]: (v4_orders_2('#skF_4'(A_139, B_617, '#skF_5'(A_139, B_143))) | ~l1_struct_0(A_139) | ~r3_waybel_9(A_139, B_617, '#skF_5'(A_139, B_143)) | ~l1_waybel_0(B_617, A_139) | ~v7_waybel_0(B_617) | ~v4_orders_2(B_617) | v2_struct_0(B_617) | ~l1_waybel_0(B_143, A_139) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_58, c_1790])).
% 7.52/2.49  tff(c_38, plain, (![C_99, A_96, B_97]: (v7_waybel_0(C_99) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_1783, plain, (![A_613, B_614, C_615]: (v7_waybel_0('#skF_4'(A_613, B_614, C_615)) | ~l1_struct_0(A_613) | ~r3_waybel_9(A_613, B_614, C_615) | ~m1_subset_1(C_615, u1_struct_0(A_613)) | ~l1_waybel_0(B_614, A_613) | ~v7_waybel_0(B_614) | ~v4_orders_2(B_614) | v2_struct_0(B_614) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(resolution, [status(thm)], [c_1743, c_38])).
% 7.52/2.49  tff(c_1789, plain, (![A_139, B_614, B_143]: (v7_waybel_0('#skF_4'(A_139, B_614, '#skF_5'(A_139, B_143))) | ~l1_struct_0(A_139) | ~r3_waybel_9(A_139, B_614, '#skF_5'(A_139, B_143)) | ~l1_waybel_0(B_614, A_139) | ~v7_waybel_0(B_614) | ~v4_orders_2(B_614) | v2_struct_0(B_614) | ~l1_waybel_0(B_143, A_139) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_58, c_1783])).
% 7.52/2.49  tff(c_1969, plain, (![B_705]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_705)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_705))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_705))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_705))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_705)) | ~l1_waybel_0(B_705, '#skF_8') | ~v7_waybel_0(B_705) | ~v4_orders_2(B_705) | v2_struct_0(B_705))), inference(splitRight, [status(thm)], [c_1921])).
% 7.52/2.49  tff(c_1973, plain, (![B_143]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1789, c_1969])).
% 7.52/2.49  tff(c_1976, plain, (![B_143]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_1658, c_1655, c_1660, c_1968, c_1973])).
% 7.52/2.49  tff(c_1978, plain, (![B_706]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_706)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_706))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_706))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_706)) | ~l1_waybel_0(B_706, '#skF_8') | ~v7_waybel_0(B_706) | ~v4_orders_2(B_706) | v2_struct_0(B_706))), inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_1976])).
% 7.52/2.49  tff(c_1982, plain, (![B_143]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1796, c_1978])).
% 7.52/2.49  tff(c_1985, plain, (![B_143]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_1658, c_1655, c_1660, c_1968, c_1982])).
% 7.52/2.49  tff(c_1987, plain, (![B_707]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707)) | ~l1_waybel_0(B_707, '#skF_8') | ~v7_waybel_0(B_707) | ~v4_orders_2(B_707) | v2_struct_0(B_707))), inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_1985])).
% 7.52/2.49  tff(c_42, plain, (![C_99, A_96, B_97]: (~v2_struct_0(C_99) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.52/2.49  tff(c_1762, plain, (![A_605, B_606, C_607]: (~v2_struct_0('#skF_4'(A_605, B_606, C_607)) | ~l1_struct_0(A_605) | ~r3_waybel_9(A_605, B_606, C_607) | ~m1_subset_1(C_607, u1_struct_0(A_605)) | ~l1_waybel_0(B_606, A_605) | ~v7_waybel_0(B_606) | ~v4_orders_2(B_606) | v2_struct_0(B_606) | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(resolution, [status(thm)], [c_1743, c_42])).
% 7.52/2.49  tff(c_1989, plain, (![B_707]: (~l1_struct_0('#skF_8') | ~m1_subset_1('#skF_5'('#skF_8', B_707), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707)) | ~l1_waybel_0(B_707, '#skF_8') | ~v7_waybel_0(B_707) | ~v4_orders_2(B_707) | v2_struct_0(B_707))), inference(resolution, [status(thm)], [c_1987, c_1762])).
% 7.52/2.49  tff(c_1992, plain, (![B_707]: (~m1_subset_1('#skF_5'('#skF_8', B_707), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8') | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_707)) | ~l1_waybel_0(B_707, '#skF_8') | ~v7_waybel_0(B_707) | ~v4_orders_2(B_707) | v2_struct_0(B_707))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1658, c_1655, c_1660, c_1968, c_1989])).
% 7.52/2.49  tff(c_1999, plain, (![B_712]: (~m1_subset_1('#skF_5'('#skF_8', B_712), u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_712)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_712)) | ~l1_waybel_0(B_712, '#skF_8') | ~v7_waybel_0(B_712) | ~v4_orders_2(B_712) | v2_struct_0(B_712))), inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_1992])).
% 7.52/2.49  tff(c_2003, plain, (![B_143]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_1999])).
% 7.52/2.49  tff(c_2006, plain, (![B_143]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_2003])).
% 7.52/2.49  tff(c_2008, plain, (![B_713]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_713)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_713)) | ~l1_waybel_0(B_713, '#skF_8') | ~v7_waybel_0(B_713) | ~v4_orders_2(B_713) | v2_struct_0(B_713))), inference(negUnitSimplification, [status(thm)], [c_80, c_2006])).
% 7.52/2.49  tff(c_1830, plain, (![C_626, A_627, B_628]: (r2_hidden(C_626, k10_yellow_6(A_627, '#skF_4'(A_627, B_628, C_626))) | ~r3_waybel_9(A_627, B_628, C_626) | ~m1_subset_1(C_626, u1_struct_0(A_627)) | ~l1_waybel_0(B_628, A_627) | ~v7_waybel_0(B_628) | ~v4_orders_2(B_628) | v2_struct_0(B_628) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(cnfTransformation, [status(thm)], [f_224])).
% 7.52/2.49  tff(c_1845, plain, (![A_627, B_628, C_626]: (~r1_tarski(k10_yellow_6(A_627, '#skF_4'(A_627, B_628, C_626)), C_626) | ~r3_waybel_9(A_627, B_628, C_626) | ~m1_subset_1(C_626, u1_struct_0(A_627)) | ~l1_waybel_0(B_628, A_627) | ~v7_waybel_0(B_628) | ~v4_orders_2(B_628) | v2_struct_0(B_628) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(resolution, [status(thm)], [c_1830, c_10])).
% 7.52/2.49  tff(c_2024, plain, (![B_713]: (~r1_tarski(k1_xboole_0, '#skF_5'('#skF_8', B_713)) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_713)) | ~m1_subset_1('#skF_5'('#skF_8', B_713), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_713)) | ~l1_waybel_0(B_713, '#skF_8') | ~v7_waybel_0(B_713) | ~v4_orders_2(B_713) | v2_struct_0(B_713))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_1845])).
% 7.52/2.49  tff(c_2057, plain, (![B_713]: (~m1_subset_1('#skF_5'('#skF_8', B_713), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_713)) | ~l1_waybel_0(B_713, '#skF_8') | ~v7_waybel_0(B_713) | ~v4_orders_2(B_713) | v2_struct_0(B_713))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1658, c_1655, c_1660, c_1666, c_2024])).
% 7.52/2.49  tff(c_2075, plain, (![B_714]: (~m1_subset_1('#skF_5'('#skF_8', B_714), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_714)) | ~l1_waybel_0(B_714, '#skF_8') | ~v7_waybel_0(B_714) | ~v4_orders_2(B_714) | v2_struct_0(B_714))), inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_2057])).
% 7.52/2.49  tff(c_2079, plain, (![B_143]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_2075])).
% 7.52/2.49  tff(c_2082, plain, (![B_143]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_143)) | ~l1_waybel_0(B_143, '#skF_8') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_2079])).
% 7.52/2.49  tff(c_2084, plain, (![B_715]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_715)) | ~l1_waybel_0(B_715, '#skF_8') | ~v7_waybel_0(B_715) | ~v4_orders_2(B_715) | v2_struct_0(B_715))), inference(negUnitSimplification, [status(thm)], [c_80, c_2082])).
% 7.52/2.49  tff(c_2092, plain, (~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_56, c_2084])).
% 7.52/2.49  tff(c_2099, plain, (v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1652, c_1658, c_1655, c_1660, c_2092])).
% 7.52/2.49  tff(c_2101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1651, c_2099])).
% 7.52/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.49  
% 7.52/2.49  Inference rules
% 7.52/2.49  ----------------------
% 7.52/2.49  #Ref     : 0
% 7.52/2.49  #Sup     : 387
% 7.52/2.49  #Fact    : 2
% 7.52/2.49  #Define  : 0
% 7.52/2.49  #Split   : 17
% 7.52/2.49  #Chain   : 0
% 7.52/2.49  #Close   : 0
% 7.52/2.49  
% 7.52/2.49  Ordering : KBO
% 7.52/2.49  
% 7.52/2.49  Simplification rules
% 7.52/2.49  ----------------------
% 7.52/2.49  #Subsume      : 90
% 7.52/2.49  #Demod        : 309
% 7.52/2.49  #Tautology    : 53
% 7.52/2.49  #SimpNegUnit  : 63
% 7.52/2.49  #BackRed      : 0
% 7.52/2.49  
% 7.52/2.49  #Partial instantiations: 0
% 7.52/2.49  #Strategies tried      : 1
% 7.52/2.49  
% 7.52/2.49  Timing (in seconds)
% 7.52/2.49  ----------------------
% 7.52/2.49  Preprocessing        : 0.42
% 7.52/2.49  Parsing              : 0.21
% 7.52/2.49  CNF conversion       : 0.04
% 7.52/2.49  Main loop            : 1.23
% 7.52/2.49  Inferencing          : 0.51
% 7.52/2.49  Reduction            : 0.28
% 7.52/2.49  Demodulation         : 0.18
% 7.52/2.49  BG Simplification    : 0.06
% 7.52/2.49  Subsumption          : 0.32
% 7.52/2.49  Abstraction          : 0.05
% 7.52/2.49  MUC search           : 0.00
% 7.52/2.49  Cooper               : 0.00
% 7.52/2.49  Total                : 1.73
% 7.52/2.49  Index Insertion      : 0.00
% 7.52/2.49  Index Deletion       : 0.00
% 7.52/2.49  Index Matching       : 0.00
% 7.52/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
