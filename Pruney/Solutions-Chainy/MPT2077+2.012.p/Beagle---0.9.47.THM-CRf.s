%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:41 EST 2020

% Result     : Theorem 5.95s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  250 (23959 expanded)
%              Number of leaves         :   45 (7970 expanded)
%              Depth                    :   47
%              Number of atoms          : 1372 (194811 expanded)
%              Number of equality atoms :   74 (9365 expanded)
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

tff(f_267,negated_conjecture,(
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

tff(f_242,axiom,(
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

tff(f_72,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
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

tff(f_162,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_189,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_116,axiom,(
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

tff(f_138,axiom,(
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

tff(f_218,axiom,(
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_82,plain,
    ( ~ v2_struct_0('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_110,plain,(
    ~ v1_compts_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_70,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_68,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_60,plain,(
    ! [A_136] :
      ( v4_orders_2('#skF_6'(A_136))
      | v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_108,plain,(
    ! [B_155] :
      ( v1_compts_1('#skF_7')
      | m2_yellow_6('#skF_9'(B_155),'#skF_7',B_155)
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_127,plain,(
    ! [B_155] :
      ( m2_yellow_6('#skF_9'(B_155),'#skF_7',B_155)
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_108])).

tff(c_12,plain,(
    ! [A_7,B_51,C_73] :
      ( m1_subset_1('#skF_2'(A_7,B_51,C_73),u1_struct_0(A_7))
      | k10_yellow_6(A_7,B_51) = C_73
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_waybel_0(B_51,A_7)
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k10_yellow_6(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_waybel_0(B_92,A_91)
      | ~ v7_waybel_0(B_92)
      | ~ v4_orders_2(B_92)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_293,plain,(
    ! [A_254,B_255,D_256] :
      ( m1_connsp_2('#skF_1'(A_254,B_255,k10_yellow_6(A_254,B_255),D_256),A_254,D_256)
      | r2_hidden(D_256,k10_yellow_6(A_254,B_255))
      | ~ m1_subset_1(D_256,u1_struct_0(A_254))
      | ~ m1_subset_1(k10_yellow_6(A_254,B_255),k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_waybel_0(B_255,A_254)
      | ~ v7_waybel_0(B_255)
      | ~ v4_orders_2(B_255)
      | v2_struct_0(B_255)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_301,plain,(
    ! [A_257,B_258,D_259] :
      ( m1_connsp_2('#skF_1'(A_257,B_258,k10_yellow_6(A_257,B_258),D_259),A_257,D_259)
      | r2_hidden(D_259,k10_yellow_6(A_257,B_258))
      | ~ m1_subset_1(D_259,u1_struct_0(A_257))
      | ~ l1_waybel_0(B_258,A_257)
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_32,c_293])).

tff(c_24,plain,(
    ! [A_7,B_51,C_73,E_90] :
      ( r2_hidden('#skF_2'(A_7,B_51,C_73),C_73)
      | r1_waybel_0(A_7,B_51,E_90)
      | ~ m1_connsp_2(E_90,A_7,'#skF_2'(A_7,B_51,C_73))
      | k10_yellow_6(A_7,B_51) = C_73
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_waybel_0(B_51,A_7)
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_407,plain,(
    ! [A_348,B_349,C_350,B_351] :
      ( r2_hidden('#skF_2'(A_348,B_349,C_350),C_350)
      | r1_waybel_0(A_348,B_349,'#skF_1'(A_348,B_351,k10_yellow_6(A_348,B_351),'#skF_2'(A_348,B_349,C_350)))
      | k10_yellow_6(A_348,B_349) = C_350
      | ~ m1_subset_1(C_350,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_waybel_0(B_349,A_348)
      | ~ v7_waybel_0(B_349)
      | ~ v4_orders_2(B_349)
      | v2_struct_0(B_349)
      | r2_hidden('#skF_2'(A_348,B_349,C_350),k10_yellow_6(A_348,B_351))
      | ~ m1_subset_1('#skF_2'(A_348,B_349,C_350),u1_struct_0(A_348))
      | ~ l1_waybel_0(B_351,A_348)
      | ~ v7_waybel_0(B_351)
      | ~ v4_orders_2(B_351)
      | v2_struct_0(B_351)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(resolution,[status(thm)],[c_301,c_24])).

tff(c_28,plain,(
    ! [A_7,B_51,D_84] :
      ( ~ r1_waybel_0(A_7,B_51,'#skF_1'(A_7,B_51,k10_yellow_6(A_7,B_51),D_84))
      | r2_hidden(D_84,k10_yellow_6(A_7,B_51))
      | ~ m1_subset_1(D_84,u1_struct_0(A_7))
      | ~ m1_subset_1(k10_yellow_6(A_7,B_51),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_waybel_0(B_51,A_7)
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_425,plain,(
    ! [A_352,B_353,C_354] :
      ( ~ m1_subset_1(k10_yellow_6(A_352,B_353),k1_zfmisc_1(u1_struct_0(A_352)))
      | r2_hidden('#skF_2'(A_352,B_353,C_354),C_354)
      | k10_yellow_6(A_352,B_353) = C_354
      | ~ m1_subset_1(C_354,k1_zfmisc_1(u1_struct_0(A_352)))
      | r2_hidden('#skF_2'(A_352,B_353,C_354),k10_yellow_6(A_352,B_353))
      | ~ m1_subset_1('#skF_2'(A_352,B_353,C_354),u1_struct_0(A_352))
      | ~ l1_waybel_0(B_353,A_352)
      | ~ v7_waybel_0(B_353)
      | ~ v4_orders_2(B_353)
      | v2_struct_0(B_353)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_407,c_28])).

tff(c_449,plain,(
    ! [A_355,B_356,C_357] :
      ( r2_hidden('#skF_2'(A_355,B_356,C_357),C_357)
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
    inference(resolution,[status(thm)],[c_32,c_425])).

tff(c_46,plain,(
    ! [A_100,B_104,C_106] :
      ( r3_waybel_9(A_100,B_104,C_106)
      | ~ r2_hidden(C_106,k10_yellow_6(A_100,B_104))
      | ~ m1_subset_1(C_106,u1_struct_0(A_100))
      | ~ l1_waybel_0(B_104,A_100)
      | ~ v7_waybel_0(B_104)
      | ~ v4_orders_2(B_104)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_474,plain,(
    ! [A_358,B_359,C_360] :
      ( r3_waybel_9(A_358,B_359,'#skF_2'(A_358,B_359,C_360))
      | r2_hidden('#skF_2'(A_358,B_359,C_360),C_360)
      | k10_yellow_6(A_358,B_359) = C_360
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_subset_1('#skF_2'(A_358,B_359,C_360),u1_struct_0(A_358))
      | ~ l1_waybel_0(B_359,A_358)
      | ~ v7_waybel_0(B_359)
      | ~ v4_orders_2(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_449,c_46])).

tff(c_478,plain,(
    ! [A_361,B_362,C_363] :
      ( r3_waybel_9(A_361,B_362,'#skF_2'(A_361,B_362,C_363))
      | r2_hidden('#skF_2'(A_361,B_362,C_363),C_363)
      | k10_yellow_6(A_361,B_362) = C_363
      | ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_waybel_0(B_362,A_361)
      | ~ v7_waybel_0(B_362)
      | ~ v4_orders_2(B_362)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(resolution,[status(thm)],[c_12,c_474])).

tff(c_486,plain,(
    ! [A_364,B_365,A_366] :
      ( r3_waybel_9(A_364,B_365,'#skF_2'(A_364,B_365,A_366))
      | r2_hidden('#skF_2'(A_364,B_365,A_366),A_366)
      | k10_yellow_6(A_364,B_365) = A_366
      | ~ l1_waybel_0(B_365,A_364)
      | ~ v7_waybel_0(B_365)
      | ~ v4_orders_2(B_365)
      | v2_struct_0(B_365)
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364)
      | v2_struct_0(A_364)
      | ~ r1_tarski(A_366,u1_struct_0(A_364)) ) ),
    inference(resolution,[status(thm)],[c_6,c_478])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(B_5,A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_508,plain,(
    ! [A_367,A_368,B_369] :
      ( ~ r1_tarski(A_367,'#skF_2'(A_368,B_369,A_367))
      | r3_waybel_9(A_368,B_369,'#skF_2'(A_368,B_369,A_367))
      | k10_yellow_6(A_368,B_369) = A_367
      | ~ l1_waybel_0(B_369,A_368)
      | ~ v7_waybel_0(B_369)
      | ~ v4_orders_2(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368)
      | ~ r1_tarski(A_367,u1_struct_0(A_368)) ) ),
    inference(resolution,[status(thm)],[c_486,c_8])).

tff(c_511,plain,(
    ! [A_368,B_369] :
      ( r3_waybel_9(A_368,B_369,'#skF_2'(A_368,B_369,k1_xboole_0))
      | k10_yellow_6(A_368,B_369) = k1_xboole_0
      | ~ l1_waybel_0(B_369,A_368)
      | ~ v7_waybel_0(B_369)
      | ~ v4_orders_2(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_368)) ) ),
    inference(resolution,[status(thm)],[c_2,c_508])).

tff(c_529,plain,(
    ! [A_374,B_375] :
      ( r3_waybel_9(A_374,B_375,'#skF_2'(A_374,B_375,k1_xboole_0))
      | k10_yellow_6(A_374,B_375) = k1_xboole_0
      | ~ l1_waybel_0(B_375,A_374)
      | ~ v7_waybel_0(B_375)
      | ~ v4_orders_2(B_375)
      | v2_struct_0(B_375)
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_511])).

tff(c_48,plain,(
    ! [A_107,B_115,D_121,C_119] :
      ( r3_waybel_9(A_107,B_115,D_121)
      | ~ r3_waybel_9(A_107,C_119,D_121)
      | ~ m1_subset_1(D_121,u1_struct_0(A_107))
      | ~ m2_yellow_6(C_119,A_107,B_115)
      | ~ l1_waybel_0(B_115,A_107)
      | ~ v7_waybel_0(B_115)
      | ~ v4_orders_2(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_786,plain,(
    ! [A_415,B_416,B_417] :
      ( r3_waybel_9(A_415,B_416,'#skF_2'(A_415,B_417,k1_xboole_0))
      | ~ m1_subset_1('#skF_2'(A_415,B_417,k1_xboole_0),u1_struct_0(A_415))
      | ~ m2_yellow_6(B_417,A_415,B_416)
      | ~ l1_waybel_0(B_416,A_415)
      | ~ v7_waybel_0(B_416)
      | ~ v4_orders_2(B_416)
      | v2_struct_0(B_416)
      | k10_yellow_6(A_415,B_417) = k1_xboole_0
      | ~ l1_waybel_0(B_417,A_415)
      | ~ v7_waybel_0(B_417)
      | ~ v4_orders_2(B_417)
      | v2_struct_0(B_417)
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(resolution,[status(thm)],[c_529,c_48])).

tff(c_791,plain,(
    ! [A_418,B_419,B_420] :
      ( r3_waybel_9(A_418,B_419,'#skF_2'(A_418,B_420,k1_xboole_0))
      | ~ m2_yellow_6(B_420,A_418,B_419)
      | ~ l1_waybel_0(B_419,A_418)
      | ~ v7_waybel_0(B_419)
      | ~ v4_orders_2(B_419)
      | v2_struct_0(B_419)
      | k10_yellow_6(A_418,B_420) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_418)))
      | ~ l1_waybel_0(B_420,A_418)
      | ~ v7_waybel_0(B_420)
      | ~ v4_orders_2(B_420)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(resolution,[status(thm)],[c_12,c_786])).

tff(c_796,plain,(
    ! [A_418,B_419,B_420] :
      ( r3_waybel_9(A_418,B_419,'#skF_2'(A_418,B_420,k1_xboole_0))
      | ~ m2_yellow_6(B_420,A_418,B_419)
      | ~ l1_waybel_0(B_419,A_418)
      | ~ v7_waybel_0(B_419)
      | ~ v4_orders_2(B_419)
      | v2_struct_0(B_419)
      | k10_yellow_6(A_418,B_420) = k1_xboole_0
      | ~ l1_waybel_0(B_420,A_418)
      | ~ v7_waybel_0(B_420)
      | ~ v4_orders_2(B_420)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_418)) ) ),
    inference(resolution,[status(thm)],[c_6,c_791])).

tff(c_801,plain,(
    ! [A_421,B_422,B_423] :
      ( r3_waybel_9(A_421,B_422,'#skF_2'(A_421,B_423,k1_xboole_0))
      | ~ m2_yellow_6(B_423,A_421,B_422)
      | ~ l1_waybel_0(B_422,A_421)
      | ~ v7_waybel_0(B_422)
      | ~ v4_orders_2(B_422)
      | v2_struct_0(B_422)
      | k10_yellow_6(A_421,B_423) = k1_xboole_0
      | ~ l1_waybel_0(B_423,A_421)
      | ~ v7_waybel_0(B_423)
      | ~ v4_orders_2(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_796])).

tff(c_54,plain,(
    ! [A_136,C_146] :
      ( ~ r3_waybel_9(A_136,'#skF_6'(A_136),C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_136))
      | v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_810,plain,(
    ! [A_424,B_425] :
      ( ~ m1_subset_1('#skF_2'(A_424,B_425,k1_xboole_0),u1_struct_0(A_424))
      | v1_compts_1(A_424)
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
    inference(resolution,[status(thm)],[c_801,c_54])).

tff(c_816,plain,(
    ! [A_426,B_427] :
      ( v1_compts_1(A_426)
      | ~ m2_yellow_6(B_427,A_426,'#skF_6'(A_426))
      | ~ l1_waybel_0('#skF_6'(A_426),A_426)
      | ~ v7_waybel_0('#skF_6'(A_426))
      | ~ v4_orders_2('#skF_6'(A_426))
      | v2_struct_0('#skF_6'(A_426))
      | k10_yellow_6(A_426,B_427) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_waybel_0(B_427,A_426)
      | ~ v7_waybel_0(B_427)
      | ~ v4_orders_2(B_427)
      | v2_struct_0(B_427)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(resolution,[status(thm)],[c_12,c_810])).

tff(c_822,plain,
    ( v1_compts_1('#skF_7')
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7')))
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
    inference(resolution,[status(thm)],[c_127,c_816])).

tff(c_826,plain,
    ( v1_compts_1('#skF_7')
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_7')
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_822])).

tff(c_827,plain,
    ( k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_826])).

tff(c_833,plain,(
    ~ v4_orders_2('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_836,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_833])).

tff(c_839,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_836])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_839])).

tff(c_843,plain,(
    v4_orders_2('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_58,plain,(
    ! [A_136] :
      ( v7_waybel_0('#skF_6'(A_136))
      | v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_842,plain,
    ( ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_844,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_850,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_844])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_850])).

tff(c_860,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_477,plain,(
    ! [A_7,B_51,C_73] :
      ( r3_waybel_9(A_7,B_51,'#skF_2'(A_7,B_51,C_73))
      | r2_hidden('#skF_2'(A_7,B_51,C_73),C_73)
      | k10_yellow_6(A_7,B_51) = C_73
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_waybel_0(B_51,A_7)
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_474])).

tff(c_862,plain,(
    ! [B_51] :
      ( r3_waybel_9('#skF_7',B_51,'#skF_2'('#skF_7',B_51,k1_xboole_0))
      | r2_hidden('#skF_2'('#skF_7',B_51,k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_7',B_51) = k1_xboole_0
      | ~ l1_waybel_0(B_51,'#skF_7')
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_860,c_477])).

tff(c_874,plain,(
    ! [B_51] :
      ( r3_waybel_9('#skF_7',B_51,'#skF_2'('#skF_7',B_51,k1_xboole_0))
      | r2_hidden('#skF_2'('#skF_7',B_51,k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_7',B_51) = k1_xboole_0
      | ~ l1_waybel_0(B_51,'#skF_7')
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_862])).

tff(c_890,plain,(
    ! [B_432] :
      ( r3_waybel_9('#skF_7',B_432,'#skF_2'('#skF_7',B_432,k1_xboole_0))
      | r2_hidden('#skF_2'('#skF_7',B_432,k1_xboole_0),k1_xboole_0)
      | k10_yellow_6('#skF_7',B_432) = k1_xboole_0
      | ~ l1_waybel_0(B_432,'#skF_7')
      | ~ v7_waybel_0(B_432)
      | ~ v4_orders_2(B_432)
      | v2_struct_0(B_432) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_874])).

tff(c_896,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),u1_struct_0('#skF_7'))
    | v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7')
    | r2_hidden('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),k1_xboole_0)
    | k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_890,c_54])).

tff(c_903,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),u1_struct_0('#skF_7'))
    | v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7')
    | r2_hidden('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),k1_xboole_0)
    | k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_70,c_68,c_896])).

tff(c_904,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),u1_struct_0('#skF_7'))
    | r2_hidden('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),k1_xboole_0)
    | k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_903])).

tff(c_905,plain,(
    ~ v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_904])).

tff(c_908,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_905])).

tff(c_911,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_908])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_911])).

tff(c_915,plain,(
    v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_56,plain,(
    ! [A_136] :
      ( l1_waybel_0('#skF_6'(A_136),A_136)
      | v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_914,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7'))
    | k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | r2_hidden('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_945,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'('#skF_7'),k1_xboole_0),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_914])).

tff(c_948,plain,
    ( k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_945])).

tff(c_951,plain,
    ( k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_843,c_915,c_860,c_948])).

tff(c_952,plain,
    ( k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_951])).

tff(c_953,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_956,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_953])).

tff(c_959,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_956])).

tff(c_961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_959])).

tff(c_963,plain,(
    l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_962,plain,
    ( v2_struct_0('#skF_6'('#skF_7'))
    | k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_964,plain,(
    k10_yellow_6('#skF_7','#skF_6'('#skF_7')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_962])).

tff(c_1011,plain,(
    ! [C_106] :
      ( r3_waybel_9('#skF_7','#skF_6'('#skF_7'),C_106)
      | ~ r2_hidden(C_106,k1_xboole_0)
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
      | ~ v7_waybel_0('#skF_6'('#skF_7'))
      | ~ v4_orders_2('#skF_6'('#skF_7'))
      | v2_struct_0('#skF_6'('#skF_7'))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_46])).

tff(c_1073,plain,(
    ! [C_106] :
      ( r3_waybel_9('#skF_7','#skF_6'('#skF_7'),C_106)
      | ~ r2_hidden(C_106,k1_xboole_0)
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_6'('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_843,c_915,c_963,c_1011])).

tff(c_1074,plain,(
    ! [C_106] :
      ( r3_waybel_9('#skF_7','#skF_6'('#skF_7'),C_106)
      | ~ r2_hidden(C_106,k1_xboole_0)
      | ~ m1_subset_1(C_106,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_6'('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1073])).

tff(c_1086,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_62,plain,(
    ! [A_136] :
      ( ~ v2_struct_0('#skF_6'(A_136))
      | v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_1090,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1086,c_62])).

tff(c_1093,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1090])).

tff(c_1095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_1093])).

tff(c_1097,plain,(
    ~ v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_130,plain,(
    ! [C_173,A_174,B_175] :
      ( ~ v2_struct_0(C_173)
      | ~ m2_yellow_6(C_173,A_174,B_175)
      | ~ l1_waybel_0(B_175,A_174)
      | ~ v7_waybel_0(B_175)
      | ~ v4_orders_2(B_175)
      | v2_struct_0(B_175)
      | ~ l1_struct_0(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_133,plain,(
    ! [B_155] :
      ( ~ v2_struct_0('#skF_9'(B_155))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(resolution,[status(thm)],[c_127,c_130])).

tff(c_136,plain,(
    ! [B_155] :
      ( ~ v2_struct_0('#skF_9'(B_155))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_133])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_140,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_140])).

tff(c_146,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_157,plain,(
    ! [C_181,A_182,B_183] :
      ( v7_waybel_0(C_181)
      | ~ m2_yellow_6(C_181,A_182,B_183)
      | ~ l1_waybel_0(B_183,A_182)
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183)
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_160,plain,(
    ! [B_155] :
      ( v7_waybel_0('#skF_9'(B_155))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(resolution,[status(thm)],[c_127,c_157])).

tff(c_163,plain,(
    ! [B_155] :
      ( v7_waybel_0('#skF_9'(B_155))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_160])).

tff(c_164,plain,(
    ! [B_155] :
      ( v7_waybel_0('#skF_9'(B_155))
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_163])).

tff(c_166,plain,(
    ! [C_185,A_186,B_187] :
      ( l1_waybel_0(C_185,A_186)
      | ~ m2_yellow_6(C_185,A_186,B_187)
      | ~ l1_waybel_0(B_187,A_186)
      | ~ v7_waybel_0(B_187)
      | ~ v4_orders_2(B_187)
      | v2_struct_0(B_187)
      | ~ l1_struct_0(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_169,plain,(
    ! [B_155] :
      ( l1_waybel_0('#skF_9'(B_155),'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(resolution,[status(thm)],[c_127,c_166])).

tff(c_172,plain,(
    ! [B_155] :
      ( l1_waybel_0('#skF_9'(B_155),'#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_169])).

tff(c_173,plain,(
    ! [B_155] :
      ( l1_waybel_0('#skF_9'(B_155),'#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_172])).

tff(c_147,plain,(
    ! [C_176,A_177,B_178] :
      ( v4_orders_2(C_176)
      | ~ m2_yellow_6(C_176,A_177,B_178)
      | ~ l1_waybel_0(B_178,A_177)
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | ~ l1_struct_0(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_150,plain,(
    ! [B_155] :
      ( v4_orders_2('#skF_9'(B_155))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(resolution,[status(thm)],[c_127,c_147])).

tff(c_153,plain,(
    ! [B_155] :
      ( v4_orders_2('#skF_9'(B_155))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_150])).

tff(c_154,plain,(
    ! [B_155] :
      ( v4_orders_2('#skF_9'(B_155))
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_153])).

tff(c_859,plain,
    ( ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_1273,plain,
    ( ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_963,c_859])).

tff(c_1274,plain,
    ( ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1273])).

tff(c_1275,plain,(
    ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_1274])).

tff(c_1278,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_154,c_1275])).

tff(c_1281,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_915,c_963,c_1278])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1281])).

tff(c_1284,plain,
    ( ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1274])).

tff(c_1286,plain,(
    ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1284])).

tff(c_1289,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_173,c_1286])).

tff(c_1292,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_915,c_963,c_1289])).

tff(c_1294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1292])).

tff(c_1295,plain,
    ( ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1298,plain,(
    ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_1301,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_164,c_1298])).

tff(c_1304,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_915,c_963,c_1301])).

tff(c_1306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1304])).

tff(c_1307,plain,
    ( v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_1310,plain,(
    k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1307])).

tff(c_96,plain,(
    ! [B_155] :
      ( v1_compts_1('#skF_7')
      | v3_yellow_6('#skF_9'(B_155),'#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_123,plain,(
    ! [B_155] :
      ( v3_yellow_6('#skF_9'(B_155),'#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_96])).

tff(c_175,plain,(
    ! [A_189,B_190] :
      ( k10_yellow_6(A_189,B_190) != k1_xboole_0
      | ~ v3_yellow_6(B_190,A_189)
      | ~ l1_waybel_0(B_190,A_189)
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_178,plain,(
    ! [B_155] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_155)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_155),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_155))
      | ~ v4_orders_2('#skF_9'(B_155))
      | v2_struct_0('#skF_9'(B_155))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(resolution,[status(thm)],[c_123,c_175])).

tff(c_181,plain,(
    ! [B_155] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_155)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_155),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_155))
      | ~ v4_orders_2('#skF_9'(B_155))
      | v2_struct_0('#skF_9'(B_155))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_178])).

tff(c_200,plain,(
    ! [B_199] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_199)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_199),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_199))
      | ~ v4_orders_2('#skF_9'(B_199))
      | v2_struct_0('#skF_9'(B_199))
      | ~ l1_waybel_0(B_199,'#skF_7')
      | ~ v7_waybel_0(B_199)
      | ~ v4_orders_2(B_199)
      | v2_struct_0(B_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_181])).

tff(c_206,plain,(
    ! [B_202] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_202)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_9'(B_202))
      | ~ v4_orders_2('#skF_9'(B_202))
      | v2_struct_0('#skF_9'(B_202))
      | ~ l1_waybel_0(B_202,'#skF_7')
      | ~ v7_waybel_0(B_202)
      | ~ v4_orders_2(B_202)
      | v2_struct_0(B_202) ) ),
    inference(resolution,[status(thm)],[c_173,c_200])).

tff(c_211,plain,(
    ! [B_203] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_203)) != k1_xboole_0
      | ~ v4_orders_2('#skF_9'(B_203))
      | v2_struct_0('#skF_9'(B_203))
      | ~ l1_waybel_0(B_203,'#skF_7')
      | ~ v7_waybel_0(B_203)
      | ~ v4_orders_2(B_203)
      | v2_struct_0(B_203) ) ),
    inference(resolution,[status(thm)],[c_164,c_206])).

tff(c_216,plain,(
    ! [B_204] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_204)) != k1_xboole_0
      | v2_struct_0('#skF_9'(B_204))
      | ~ l1_waybel_0(B_204,'#skF_7')
      | ~ v7_waybel_0(B_204)
      | ~ v4_orders_2(B_204)
      | v2_struct_0(B_204) ) ),
    inference(resolution,[status(thm)],[c_154,c_211])).

tff(c_145,plain,(
    ! [B_155] :
      ( ~ v2_struct_0('#skF_9'(B_155))
      | ~ l1_waybel_0(B_155,'#skF_7')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_220,plain,(
    ! [B_204] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_204)) != k1_xboole_0
      | ~ l1_waybel_0(B_204,'#skF_7')
      | ~ v7_waybel_0(B_204)
      | ~ v4_orders_2(B_204)
      | v2_struct_0(B_204) ) ),
    inference(resolution,[status(thm)],[c_216,c_145])).

tff(c_1361,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_220])).

tff(c_1426,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_915,c_963,c_1361])).

tff(c_1428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1426])).

tff(c_1429,plain,(
    v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_1307])).

tff(c_1433,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1429,c_145])).

tff(c_1436,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_915,c_963,c_1433])).

tff(c_1438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1436])).

tff(c_1439,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1440,plain,(
    v1_compts_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_80,plain,
    ( v4_orders_2('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_1445,plain,(
    v4_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_80])).

tff(c_78,plain,
    ( v7_waybel_0('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_1442,plain,(
    v7_waybel_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_78])).

tff(c_76,plain,
    ( l1_waybel_0('#skF_8','#skF_7')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_1447,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_76])).

tff(c_64,plain,(
    ! [A_136,B_143] :
      ( r3_waybel_9(A_136,B_143,'#skF_5'(A_136,B_143))
      | ~ l1_waybel_0(B_143,A_136)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_66,plain,(
    ! [A_136,B_143] :
      ( m1_subset_1('#skF_5'(A_136,B_143),u1_struct_0(A_136))
      | ~ l1_waybel_0(B_143,A_136)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_1495,plain,(
    ! [A_504,B_505,C_506] :
      ( m2_yellow_6('#skF_4'(A_504,B_505,C_506),A_504,B_505)
      | ~ r3_waybel_9(A_504,B_505,C_506)
      | ~ m1_subset_1(C_506,u1_struct_0(A_504))
      | ~ l1_waybel_0(B_505,A_504)
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_34,plain,(
    ! [C_96,A_93,B_94] :
      ( l1_waybel_0(C_96,A_93)
      | ~ m2_yellow_6(C_96,A_93,B_94)
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1574,plain,(
    ! [A_528,B_529,C_530] :
      ( l1_waybel_0('#skF_4'(A_528,B_529,C_530),A_528)
      | ~ l1_struct_0(A_528)
      | ~ r3_waybel_9(A_528,B_529,C_530)
      | ~ m1_subset_1(C_530,u1_struct_0(A_528))
      | ~ l1_waybel_0(B_529,A_528)
      | ~ v7_waybel_0(B_529)
      | ~ v4_orders_2(B_529)
      | v2_struct_0(B_529)
      | ~ l1_pre_topc(A_528)
      | ~ v2_pre_topc(A_528)
      | v2_struct_0(A_528) ) ),
    inference(resolution,[status(thm)],[c_1495,c_34])).

tff(c_1639,plain,(
    ! [A_578,B_579,B_580] :
      ( l1_waybel_0('#skF_4'(A_578,B_579,'#skF_5'(A_578,B_580)),A_578)
      | ~ l1_struct_0(A_578)
      | ~ r3_waybel_9(A_578,B_579,'#skF_5'(A_578,B_580))
      | ~ l1_waybel_0(B_579,A_578)
      | ~ v7_waybel_0(B_579)
      | ~ v4_orders_2(B_579)
      | v2_struct_0(B_579)
      | ~ l1_waybel_0(B_580,A_578)
      | ~ v7_waybel_0(B_580)
      | ~ v4_orders_2(B_580)
      | v2_struct_0(B_580)
      | ~ v1_compts_1(A_578)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | v2_struct_0(A_578) ) ),
    inference(resolution,[status(thm)],[c_66,c_1574])).

tff(c_42,plain,(
    ! [B_99,A_97] :
      ( v3_yellow_6(B_99,A_97)
      | k10_yellow_6(A_97,B_99) = k1_xboole_0
      | ~ l1_waybel_0(B_99,A_97)
      | ~ v7_waybel_0(B_99)
      | ~ v4_orders_2(B_99)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_74,plain,(
    ! [C_154] :
      ( ~ v3_yellow_6(C_154,'#skF_7')
      | ~ m2_yellow_6(C_154,'#skF_7','#skF_8')
      | ~ v1_compts_1('#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_1456,plain,(
    ! [C_154] :
      ( ~ v3_yellow_6(C_154,'#skF_7')
      | ~ m2_yellow_6(C_154,'#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_74])).

tff(c_1511,plain,(
    ! [C_506] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_506),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_506)
      | ~ m1_subset_1(C_506,u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1495,c_1456])).

tff(c_1518,plain,(
    ! [C_506] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_506),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_506)
      | ~ m1_subset_1(C_506,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1445,c_1442,c_1447,c_1511])).

tff(c_1520,plain,(
    ! [C_507] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_507),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_507)
      | ~ m1_subset_1(C_507,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1518])).

tff(c_1523,plain,(
    ! [C_507] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_507)
      | ~ m1_subset_1(C_507,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_507)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_507),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_507))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_507))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_507))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_1520])).

tff(c_1526,plain,(
    ! [C_507] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_507)
      | ~ m1_subset_1(C_507,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_507)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_507),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_507))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_507))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_507))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1523])).

tff(c_1548,plain,(
    ! [C_524] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_524)
      | ~ m1_subset_1(C_524,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_524)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_524),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_524))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_524))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_524)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1526])).

tff(c_1556,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1548])).

tff(c_1563,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1556])).

tff(c_1564,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1563])).

tff(c_1643,plain,(
    ! [B_580] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_580))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_580,'#skF_7')
      | ~ v7_waybel_0(B_580)
      | ~ v4_orders_2(B_580)
      | v2_struct_0(B_580)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1639,c_1564])).

tff(c_1646,plain,(
    ! [B_580] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_580))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_580,'#skF_7')
      | ~ v7_waybel_0(B_580)
      | ~ v4_orders_2(B_580)
      | v2_struct_0(B_580)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1445,c_1442,c_1447,c_1643])).

tff(c_1647,plain,(
    ! [B_580] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_580)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_580))
      | ~ l1_waybel_0(B_580,'#skF_7')
      | ~ v7_waybel_0(B_580)
      | ~ v4_orders_2(B_580)
      | v2_struct_0(B_580) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1646])).

tff(c_1648,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1647])).

tff(c_1651,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_1648])).

tff(c_1655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1651])).

tff(c_1657,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1647])).

tff(c_38,plain,(
    ! [C_96,A_93,B_94] :
      ( v4_orders_2(C_96)
      | ~ m2_yellow_6(C_96,A_93,B_94)
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1528,plain,(
    ! [A_508,B_509,C_510] :
      ( v4_orders_2('#skF_4'(A_508,B_509,C_510))
      | ~ l1_struct_0(A_508)
      | ~ r3_waybel_9(A_508,B_509,C_510)
      | ~ m1_subset_1(C_510,u1_struct_0(A_508))
      | ~ l1_waybel_0(B_509,A_508)
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509)
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_1495,c_38])).

tff(c_1531,plain,(
    ! [A_136,B_509,B_143] :
      ( v4_orders_2('#skF_4'(A_136,B_509,'#skF_5'(A_136,B_143)))
      | ~ l1_struct_0(A_136)
      | ~ r3_waybel_9(A_136,B_509,'#skF_5'(A_136,B_143))
      | ~ l1_waybel_0(B_509,A_136)
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509)
      | ~ l1_waybel_0(B_143,A_136)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_66,c_1528])).

tff(c_36,plain,(
    ! [C_96,A_93,B_94] :
      ( v7_waybel_0(C_96)
      | ~ m2_yellow_6(C_96,A_93,B_94)
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1537,plain,(
    ! [A_517,B_518,C_519] :
      ( v7_waybel_0('#skF_4'(A_517,B_518,C_519))
      | ~ l1_struct_0(A_517)
      | ~ r3_waybel_9(A_517,B_518,C_519)
      | ~ m1_subset_1(C_519,u1_struct_0(A_517))
      | ~ l1_waybel_0(B_518,A_517)
      | ~ v7_waybel_0(B_518)
      | ~ v4_orders_2(B_518)
      | v2_struct_0(B_518)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(resolution,[status(thm)],[c_1495,c_36])).

tff(c_1543,plain,(
    ! [A_136,B_518,B_143] :
      ( v7_waybel_0('#skF_4'(A_136,B_518,'#skF_5'(A_136,B_143)))
      | ~ l1_struct_0(A_136)
      | ~ r3_waybel_9(A_136,B_518,'#skF_5'(A_136,B_143))
      | ~ l1_waybel_0(B_518,A_136)
      | ~ v7_waybel_0(B_518)
      | ~ v4_orders_2(B_518)
      | v2_struct_0(B_518)
      | ~ l1_waybel_0(B_143,A_136)
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1(A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_66,c_1537])).

tff(c_1658,plain,(
    ! [B_581] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_581))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_581)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_581)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_581)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_581))
      | ~ l1_waybel_0(B_581,'#skF_7')
      | ~ v7_waybel_0(B_581)
      | ~ v4_orders_2(B_581)
      | v2_struct_0(B_581) ) ),
    inference(splitRight,[status(thm)],[c_1647])).

tff(c_1662,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1543,c_1658])).

tff(c_1665,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1445,c_1442,c_1447,c_1657,c_1662])).

tff(c_1667,plain,(
    ! [B_582] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_582))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_582)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_582)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_582))
      | ~ l1_waybel_0(B_582,'#skF_7')
      | ~ v7_waybel_0(B_582)
      | ~ v4_orders_2(B_582)
      | v2_struct_0(B_582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1665])).

tff(c_1671,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1531,c_1667])).

tff(c_1674,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1445,c_1442,c_1447,c_1657,c_1671])).

tff(c_1676,plain,(
    ! [B_583] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_583))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_583)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_583))
      | ~ l1_waybel_0(B_583,'#skF_7')
      | ~ v7_waybel_0(B_583)
      | ~ v4_orders_2(B_583)
      | v2_struct_0(B_583) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1674])).

tff(c_40,plain,(
    ! [C_96,A_93,B_94] :
      ( ~ v2_struct_0(C_96)
      | ~ m2_yellow_6(C_96,A_93,B_94)
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1514,plain,(
    ! [A_504,B_505,C_506] :
      ( ~ v2_struct_0('#skF_4'(A_504,B_505,C_506))
      | ~ l1_struct_0(A_504)
      | ~ r3_waybel_9(A_504,B_505,C_506)
      | ~ m1_subset_1(C_506,u1_struct_0(A_504))
      | ~ l1_waybel_0(B_505,A_504)
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(resolution,[status(thm)],[c_1495,c_40])).

tff(c_1678,plain,(
    ! [B_583] :
      ( ~ l1_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_7',B_583),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_583))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_583))
      | ~ l1_waybel_0(B_583,'#skF_7')
      | ~ v7_waybel_0(B_583)
      | ~ v4_orders_2(B_583)
      | v2_struct_0(B_583) ) ),
    inference(resolution,[status(thm)],[c_1676,c_1514])).

tff(c_1681,plain,(
    ! [B_583] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_583),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7')
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_583))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_583))
      | ~ l1_waybel_0(B_583,'#skF_7')
      | ~ v7_waybel_0(B_583)
      | ~ v4_orders_2(B_583)
      | v2_struct_0(B_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1445,c_1442,c_1447,c_1657,c_1678])).

tff(c_1687,plain,(
    ! [B_587] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_587),u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_587))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_587))
      | ~ l1_waybel_0(B_587,'#skF_7')
      | ~ v7_waybel_0(B_587)
      | ~ v4_orders_2(B_587)
      | v2_struct_0(B_587) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1681])).

tff(c_1691,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1687])).

tff(c_1694,plain,(
    ! [B_143] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1691])).

tff(c_1696,plain,(
    ! [B_588] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_588))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_588))
      | ~ l1_waybel_0(B_588,'#skF_7')
      | ~ v7_waybel_0(B_588)
      | ~ v4_orders_2(B_588)
      | v2_struct_0(B_588) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1694])).

tff(c_1565,plain,(
    ! [C_525,A_526,B_527] :
      ( r2_hidden(C_525,k10_yellow_6(A_526,'#skF_4'(A_526,B_527,C_525)))
      | ~ r3_waybel_9(A_526,B_527,C_525)
      | ~ m1_subset_1(C_525,u1_struct_0(A_526))
      | ~ l1_waybel_0(B_527,A_526)
      | ~ v7_waybel_0(B_527)
      | ~ v4_orders_2(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_526)
      | ~ v2_pre_topc(A_526)
      | v2_struct_0(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1573,plain,(
    ! [A_526,B_527,C_525] :
      ( ~ r1_tarski(k10_yellow_6(A_526,'#skF_4'(A_526,B_527,C_525)),C_525)
      | ~ r3_waybel_9(A_526,B_527,C_525)
      | ~ m1_subset_1(C_525,u1_struct_0(A_526))
      | ~ l1_waybel_0(B_527,A_526)
      | ~ v7_waybel_0(B_527)
      | ~ v4_orders_2(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_526)
      | ~ v2_pre_topc(A_526)
      | v2_struct_0(A_526) ) ),
    inference(resolution,[status(thm)],[c_1565,c_8])).

tff(c_1707,plain,(
    ! [B_588] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5'('#skF_7',B_588))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_588))
      | ~ m1_subset_1('#skF_5'('#skF_7',B_588),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_588))
      | ~ l1_waybel_0(B_588,'#skF_7')
      | ~ v7_waybel_0(B_588)
      | ~ v4_orders_2(B_588)
      | v2_struct_0(B_588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1696,c_1573])).

tff(c_1731,plain,(
    ! [B_588] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_588),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_588))
      | ~ l1_waybel_0(B_588,'#skF_7')
      | ~ v7_waybel_0(B_588)
      | ~ v4_orders_2(B_588)
      | v2_struct_0(B_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1445,c_1442,c_1447,c_2,c_1707])).

tff(c_1746,plain,(
    ! [B_589] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_589),u1_struct_0('#skF_7'))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_589))
      | ~ l1_waybel_0(B_589,'#skF_7')
      | ~ v7_waybel_0(B_589)
      | ~ v4_orders_2(B_589)
      | v2_struct_0(B_589) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1731])).

tff(c_1750,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1746])).

tff(c_1753,plain,(
    ! [B_143] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_143))
      | ~ l1_waybel_0(B_143,'#skF_7')
      | ~ v7_waybel_0(B_143)
      | ~ v4_orders_2(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1750])).

tff(c_1755,plain,(
    ! [B_590] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_590))
      | ~ l1_waybel_0(B_590,'#skF_7')
      | ~ v7_waybel_0(B_590)
      | ~ v4_orders_2(B_590)
      | v2_struct_0(B_590) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1753])).

tff(c_1763,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_1755])).

tff(c_1770,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1440,c_1445,c_1442,c_1447,c_1763])).

tff(c_1772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1439,c_1770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.95/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.17  
% 5.95/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.17  %$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_9 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6
% 5.95/2.17  
% 5.95/2.17  %Foreground sorts:
% 5.95/2.17  
% 5.95/2.17  
% 5.95/2.17  %Background operators:
% 5.95/2.17  
% 5.95/2.17  
% 5.95/2.17  %Foreground operators:
% 5.95/2.17  tff('#skF_9', type, '#skF_9': $i > $i).
% 5.95/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.95/2.17  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 5.95/2.17  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.95/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.95/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.95/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.95/2.17  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.95/2.17  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 5.95/2.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.95/2.17  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.95/2.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.95/2.17  tff('#skF_7', type, '#skF_7': $i).
% 5.95/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.95/2.17  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.95/2.17  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 5.95/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.95/2.17  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.95/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.95/2.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.95/2.17  tff('#skF_8', type, '#skF_8': $i).
% 5.95/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.95/2.17  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.95/2.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.95/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.95/2.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.95/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.95/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.95/2.17  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.95/2.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.95/2.17  tff('#skF_6', type, '#skF_6': $i > $i).
% 5.95/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.95/2.17  
% 5.95/2.21  tff(f_267, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 5.95/2.21  tff(f_242, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 5.95/2.21  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 5.95/2.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.95/2.21  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.95/2.21  tff(f_90, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 5.95/2.21  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 5.95/2.21  tff(f_36, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.95/2.21  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 5.95/2.21  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.95/2.21  tff(f_116, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 5.95/2.21  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 5.95/2.21  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 5.95/2.21  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_82, plain, (~v2_struct_0('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_110, plain, (~v1_compts_1('#skF_7')), inference(splitLeft, [status(thm)], [c_82])).
% 5.95/2.21  tff(c_70, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_68, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_60, plain, (![A_136]: (v4_orders_2('#skF_6'(A_136)) | v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_108, plain, (![B_155]: (v1_compts_1('#skF_7') | m2_yellow_6('#skF_9'(B_155), '#skF_7', B_155) | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_127, plain, (![B_155]: (m2_yellow_6('#skF_9'(B_155), '#skF_7', B_155) | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(negUnitSimplification, [status(thm)], [c_110, c_108])).
% 5.95/2.21  tff(c_12, plain, (![A_7, B_51, C_73]: (m1_subset_1('#skF_2'(A_7, B_51, C_73), u1_struct_0(A_7)) | k10_yellow_6(A_7, B_51)=C_73 | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_waybel_0(B_51, A_7) | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.95/2.21  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.95/2.21  tff(c_32, plain, (![A_91, B_92]: (m1_subset_1(k10_yellow_6(A_91, B_92), k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_waybel_0(B_92, A_91) | ~v7_waybel_0(B_92) | ~v4_orders_2(B_92) | v2_struct_0(B_92) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.95/2.21  tff(c_293, plain, (![A_254, B_255, D_256]: (m1_connsp_2('#skF_1'(A_254, B_255, k10_yellow_6(A_254, B_255), D_256), A_254, D_256) | r2_hidden(D_256, k10_yellow_6(A_254, B_255)) | ~m1_subset_1(D_256, u1_struct_0(A_254)) | ~m1_subset_1(k10_yellow_6(A_254, B_255), k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_waybel_0(B_255, A_254) | ~v7_waybel_0(B_255) | ~v4_orders_2(B_255) | v2_struct_0(B_255) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254) | v2_struct_0(A_254))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.21  tff(c_301, plain, (![A_257, B_258, D_259]: (m1_connsp_2('#skF_1'(A_257, B_258, k10_yellow_6(A_257, B_258), D_259), A_257, D_259) | r2_hidden(D_259, k10_yellow_6(A_257, B_258)) | ~m1_subset_1(D_259, u1_struct_0(A_257)) | ~l1_waybel_0(B_258, A_257) | ~v7_waybel_0(B_258) | ~v4_orders_2(B_258) | v2_struct_0(B_258) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_32, c_293])).
% 5.95/2.21  tff(c_24, plain, (![A_7, B_51, C_73, E_90]: (r2_hidden('#skF_2'(A_7, B_51, C_73), C_73) | r1_waybel_0(A_7, B_51, E_90) | ~m1_connsp_2(E_90, A_7, '#skF_2'(A_7, B_51, C_73)) | k10_yellow_6(A_7, B_51)=C_73 | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_waybel_0(B_51, A_7) | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.21  tff(c_407, plain, (![A_348, B_349, C_350, B_351]: (r2_hidden('#skF_2'(A_348, B_349, C_350), C_350) | r1_waybel_0(A_348, B_349, '#skF_1'(A_348, B_351, k10_yellow_6(A_348, B_351), '#skF_2'(A_348, B_349, C_350))) | k10_yellow_6(A_348, B_349)=C_350 | ~m1_subset_1(C_350, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_waybel_0(B_349, A_348) | ~v7_waybel_0(B_349) | ~v4_orders_2(B_349) | v2_struct_0(B_349) | r2_hidden('#skF_2'(A_348, B_349, C_350), k10_yellow_6(A_348, B_351)) | ~m1_subset_1('#skF_2'(A_348, B_349, C_350), u1_struct_0(A_348)) | ~l1_waybel_0(B_351, A_348) | ~v7_waybel_0(B_351) | ~v4_orders_2(B_351) | v2_struct_0(B_351) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348) | v2_struct_0(A_348))), inference(resolution, [status(thm)], [c_301, c_24])).
% 5.95/2.21  tff(c_28, plain, (![A_7, B_51, D_84]: (~r1_waybel_0(A_7, B_51, '#skF_1'(A_7, B_51, k10_yellow_6(A_7, B_51), D_84)) | r2_hidden(D_84, k10_yellow_6(A_7, B_51)) | ~m1_subset_1(D_84, u1_struct_0(A_7)) | ~m1_subset_1(k10_yellow_6(A_7, B_51), k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_waybel_0(B_51, A_7) | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.95/2.21  tff(c_425, plain, (![A_352, B_353, C_354]: (~m1_subset_1(k10_yellow_6(A_352, B_353), k1_zfmisc_1(u1_struct_0(A_352))) | r2_hidden('#skF_2'(A_352, B_353, C_354), C_354) | k10_yellow_6(A_352, B_353)=C_354 | ~m1_subset_1(C_354, k1_zfmisc_1(u1_struct_0(A_352))) | r2_hidden('#skF_2'(A_352, B_353, C_354), k10_yellow_6(A_352, B_353)) | ~m1_subset_1('#skF_2'(A_352, B_353, C_354), u1_struct_0(A_352)) | ~l1_waybel_0(B_353, A_352) | ~v7_waybel_0(B_353) | ~v4_orders_2(B_353) | v2_struct_0(B_353) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(resolution, [status(thm)], [c_407, c_28])).
% 5.95/2.21  tff(c_449, plain, (![A_355, B_356, C_357]: (r2_hidden('#skF_2'(A_355, B_356, C_357), C_357) | k10_yellow_6(A_355, B_356)=C_357 | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0(A_355))) | r2_hidden('#skF_2'(A_355, B_356, C_357), k10_yellow_6(A_355, B_356)) | ~m1_subset_1('#skF_2'(A_355, B_356, C_357), u1_struct_0(A_355)) | ~l1_waybel_0(B_356, A_355) | ~v7_waybel_0(B_356) | ~v4_orders_2(B_356) | v2_struct_0(B_356) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355))), inference(resolution, [status(thm)], [c_32, c_425])).
% 5.95/2.21  tff(c_46, plain, (![A_100, B_104, C_106]: (r3_waybel_9(A_100, B_104, C_106) | ~r2_hidden(C_106, k10_yellow_6(A_100, B_104)) | ~m1_subset_1(C_106, u1_struct_0(A_100)) | ~l1_waybel_0(B_104, A_100) | ~v7_waybel_0(B_104) | ~v4_orders_2(B_104) | v2_struct_0(B_104) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.95/2.21  tff(c_474, plain, (![A_358, B_359, C_360]: (r3_waybel_9(A_358, B_359, '#skF_2'(A_358, B_359, C_360)) | r2_hidden('#skF_2'(A_358, B_359, C_360), C_360) | k10_yellow_6(A_358, B_359)=C_360 | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(A_358))) | ~m1_subset_1('#skF_2'(A_358, B_359, C_360), u1_struct_0(A_358)) | ~l1_waybel_0(B_359, A_358) | ~v7_waybel_0(B_359) | ~v4_orders_2(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(resolution, [status(thm)], [c_449, c_46])).
% 5.95/2.21  tff(c_478, plain, (![A_361, B_362, C_363]: (r3_waybel_9(A_361, B_362, '#skF_2'(A_361, B_362, C_363)) | r2_hidden('#skF_2'(A_361, B_362, C_363), C_363) | k10_yellow_6(A_361, B_362)=C_363 | ~m1_subset_1(C_363, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_waybel_0(B_362, A_361) | ~v7_waybel_0(B_362) | ~v4_orders_2(B_362) | v2_struct_0(B_362) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361) | v2_struct_0(A_361))), inference(resolution, [status(thm)], [c_12, c_474])).
% 5.95/2.21  tff(c_486, plain, (![A_364, B_365, A_366]: (r3_waybel_9(A_364, B_365, '#skF_2'(A_364, B_365, A_366)) | r2_hidden('#skF_2'(A_364, B_365, A_366), A_366) | k10_yellow_6(A_364, B_365)=A_366 | ~l1_waybel_0(B_365, A_364) | ~v7_waybel_0(B_365) | ~v4_orders_2(B_365) | v2_struct_0(B_365) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364) | v2_struct_0(A_364) | ~r1_tarski(A_366, u1_struct_0(A_364)))), inference(resolution, [status(thm)], [c_6, c_478])).
% 5.95/2.21  tff(c_8, plain, (![B_5, A_4]: (~r1_tarski(B_5, A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.95/2.21  tff(c_508, plain, (![A_367, A_368, B_369]: (~r1_tarski(A_367, '#skF_2'(A_368, B_369, A_367)) | r3_waybel_9(A_368, B_369, '#skF_2'(A_368, B_369, A_367)) | k10_yellow_6(A_368, B_369)=A_367 | ~l1_waybel_0(B_369, A_368) | ~v7_waybel_0(B_369) | ~v4_orders_2(B_369) | v2_struct_0(B_369) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368) | ~r1_tarski(A_367, u1_struct_0(A_368)))), inference(resolution, [status(thm)], [c_486, c_8])).
% 5.95/2.21  tff(c_511, plain, (![A_368, B_369]: (r3_waybel_9(A_368, B_369, '#skF_2'(A_368, B_369, k1_xboole_0)) | k10_yellow_6(A_368, B_369)=k1_xboole_0 | ~l1_waybel_0(B_369, A_368) | ~v7_waybel_0(B_369) | ~v4_orders_2(B_369) | v2_struct_0(B_369) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_368)))), inference(resolution, [status(thm)], [c_2, c_508])).
% 5.95/2.21  tff(c_529, plain, (![A_374, B_375]: (r3_waybel_9(A_374, B_375, '#skF_2'(A_374, B_375, k1_xboole_0)) | k10_yellow_6(A_374, B_375)=k1_xboole_0 | ~l1_waybel_0(B_375, A_374) | ~v7_waybel_0(B_375) | ~v4_orders_2(B_375) | v2_struct_0(B_375) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_511])).
% 5.95/2.21  tff(c_48, plain, (![A_107, B_115, D_121, C_119]: (r3_waybel_9(A_107, B_115, D_121) | ~r3_waybel_9(A_107, C_119, D_121) | ~m1_subset_1(D_121, u1_struct_0(A_107)) | ~m2_yellow_6(C_119, A_107, B_115) | ~l1_waybel_0(B_115, A_107) | ~v7_waybel_0(B_115) | ~v4_orders_2(B_115) | v2_struct_0(B_115) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.95/2.21  tff(c_786, plain, (![A_415, B_416, B_417]: (r3_waybel_9(A_415, B_416, '#skF_2'(A_415, B_417, k1_xboole_0)) | ~m1_subset_1('#skF_2'(A_415, B_417, k1_xboole_0), u1_struct_0(A_415)) | ~m2_yellow_6(B_417, A_415, B_416) | ~l1_waybel_0(B_416, A_415) | ~v7_waybel_0(B_416) | ~v4_orders_2(B_416) | v2_struct_0(B_416) | k10_yellow_6(A_415, B_417)=k1_xboole_0 | ~l1_waybel_0(B_417, A_415) | ~v7_waybel_0(B_417) | ~v4_orders_2(B_417) | v2_struct_0(B_417) | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(resolution, [status(thm)], [c_529, c_48])).
% 5.95/2.21  tff(c_791, plain, (![A_418, B_419, B_420]: (r3_waybel_9(A_418, B_419, '#skF_2'(A_418, B_420, k1_xboole_0)) | ~m2_yellow_6(B_420, A_418, B_419) | ~l1_waybel_0(B_419, A_418) | ~v7_waybel_0(B_419) | ~v4_orders_2(B_419) | v2_struct_0(B_419) | k10_yellow_6(A_418, B_420)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_418))) | ~l1_waybel_0(B_420, A_418) | ~v7_waybel_0(B_420) | ~v4_orders_2(B_420) | v2_struct_0(B_420) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(resolution, [status(thm)], [c_12, c_786])).
% 5.95/2.21  tff(c_796, plain, (![A_418, B_419, B_420]: (r3_waybel_9(A_418, B_419, '#skF_2'(A_418, B_420, k1_xboole_0)) | ~m2_yellow_6(B_420, A_418, B_419) | ~l1_waybel_0(B_419, A_418) | ~v7_waybel_0(B_419) | ~v4_orders_2(B_419) | v2_struct_0(B_419) | k10_yellow_6(A_418, B_420)=k1_xboole_0 | ~l1_waybel_0(B_420, A_418) | ~v7_waybel_0(B_420) | ~v4_orders_2(B_420) | v2_struct_0(B_420) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_418)))), inference(resolution, [status(thm)], [c_6, c_791])).
% 5.95/2.21  tff(c_801, plain, (![A_421, B_422, B_423]: (r3_waybel_9(A_421, B_422, '#skF_2'(A_421, B_423, k1_xboole_0)) | ~m2_yellow_6(B_423, A_421, B_422) | ~l1_waybel_0(B_422, A_421) | ~v7_waybel_0(B_422) | ~v4_orders_2(B_422) | v2_struct_0(B_422) | k10_yellow_6(A_421, B_423)=k1_xboole_0 | ~l1_waybel_0(B_423, A_421) | ~v7_waybel_0(B_423) | ~v4_orders_2(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_796])).
% 5.95/2.21  tff(c_54, plain, (![A_136, C_146]: (~r3_waybel_9(A_136, '#skF_6'(A_136), C_146) | ~m1_subset_1(C_146, u1_struct_0(A_136)) | v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_810, plain, (![A_424, B_425]: (~m1_subset_1('#skF_2'(A_424, B_425, k1_xboole_0), u1_struct_0(A_424)) | v1_compts_1(A_424) | ~m2_yellow_6(B_425, A_424, '#skF_6'(A_424)) | ~l1_waybel_0('#skF_6'(A_424), A_424) | ~v7_waybel_0('#skF_6'(A_424)) | ~v4_orders_2('#skF_6'(A_424)) | v2_struct_0('#skF_6'(A_424)) | k10_yellow_6(A_424, B_425)=k1_xboole_0 | ~l1_waybel_0(B_425, A_424) | ~v7_waybel_0(B_425) | ~v4_orders_2(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(resolution, [status(thm)], [c_801, c_54])).
% 5.95/2.21  tff(c_816, plain, (![A_426, B_427]: (v1_compts_1(A_426) | ~m2_yellow_6(B_427, A_426, '#skF_6'(A_426)) | ~l1_waybel_0('#skF_6'(A_426), A_426) | ~v7_waybel_0('#skF_6'(A_426)) | ~v4_orders_2('#skF_6'(A_426)) | v2_struct_0('#skF_6'(A_426)) | k10_yellow_6(A_426, B_427)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_waybel_0(B_427, A_426) | ~v7_waybel_0(B_427) | ~v4_orders_2(B_427) | v2_struct_0(B_427) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(resolution, [status(thm)], [c_12, c_810])).
% 5.95/2.21  tff(c_822, plain, (v1_compts_1('#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_127, c_816])).
% 5.95/2.21  tff(c_826, plain, (v1_compts_1('#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_822])).
% 5.95/2.21  tff(c_827, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_826])).
% 5.95/2.21  tff(c_833, plain, (~v4_orders_2('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_827])).
% 5.95/2.21  tff(c_836, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_833])).
% 5.95/2.21  tff(c_839, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_836])).
% 5.95/2.21  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_839])).
% 5.95/2.21  tff(c_843, plain, (v4_orders_2('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_827])).
% 5.95/2.21  tff(c_58, plain, (![A_136]: (v7_waybel_0('#skF_6'(A_136)) | v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_842, plain, (~v7_waybel_0('#skF_6'('#skF_7')) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_827])).
% 5.95/2.21  tff(c_844, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_842])).
% 5.95/2.21  tff(c_850, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_844])).
% 5.95/2.21  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_850])).
% 5.95/2.21  tff(c_860, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_842])).
% 5.95/2.21  tff(c_477, plain, (![A_7, B_51, C_73]: (r3_waybel_9(A_7, B_51, '#skF_2'(A_7, B_51, C_73)) | r2_hidden('#skF_2'(A_7, B_51, C_73), C_73) | k10_yellow_6(A_7, B_51)=C_73 | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_waybel_0(B_51, A_7) | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(resolution, [status(thm)], [c_12, c_474])).
% 5.95/2.21  tff(c_862, plain, (![B_51]: (r3_waybel_9('#skF_7', B_51, '#skF_2'('#skF_7', B_51, k1_xboole_0)) | r2_hidden('#skF_2'('#skF_7', B_51, k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_7', B_51)=k1_xboole_0 | ~l1_waybel_0(B_51, '#skF_7') | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_860, c_477])).
% 5.95/2.21  tff(c_874, plain, (![B_51]: (r3_waybel_9('#skF_7', B_51, '#skF_2'('#skF_7', B_51, k1_xboole_0)) | r2_hidden('#skF_2'('#skF_7', B_51, k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_7', B_51)=k1_xboole_0 | ~l1_waybel_0(B_51, '#skF_7') | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_862])).
% 5.95/2.21  tff(c_890, plain, (![B_432]: (r3_waybel_9('#skF_7', B_432, '#skF_2'('#skF_7', B_432, k1_xboole_0)) | r2_hidden('#skF_2'('#skF_7', B_432, k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_7', B_432)=k1_xboole_0 | ~l1_waybel_0(B_432, '#skF_7') | ~v7_waybel_0(B_432) | ~v4_orders_2(B_432) | v2_struct_0(B_432))), inference(negUnitSimplification, [status(thm)], [c_72, c_874])).
% 5.95/2.21  tff(c_896, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), u1_struct_0('#skF_7')) | v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | r2_hidden('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_890, c_54])).
% 5.95/2.21  tff(c_903, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), u1_struct_0('#skF_7')) | v1_compts_1('#skF_7') | v2_struct_0('#skF_7') | r2_hidden('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_70, c_68, c_896])).
% 5.95/2.21  tff(c_904, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), u1_struct_0('#skF_7')) | r2_hidden('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), k1_xboole_0) | k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_903])).
% 5.95/2.21  tff(c_905, plain, (~v7_waybel_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_904])).
% 5.95/2.21  tff(c_908, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_905])).
% 5.95/2.21  tff(c_911, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_908])).
% 5.95/2.21  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_911])).
% 5.95/2.21  tff(c_915, plain, (v7_waybel_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_904])).
% 5.95/2.21  tff(c_56, plain, (![A_136]: (l1_waybel_0('#skF_6'(A_136), A_136) | v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_914, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), u1_struct_0('#skF_7')) | v2_struct_0('#skF_6'('#skF_7')) | k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | r2_hidden('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_904])).
% 5.95/2.21  tff(c_945, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'('#skF_7'), k1_xboole_0), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_914])).
% 5.95/2.21  tff(c_948, plain, (k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_12, c_945])).
% 5.95/2.21  tff(c_951, plain, (k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_843, c_915, c_860, c_948])).
% 5.95/2.21  tff(c_952, plain, (k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | v2_struct_0('#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_951])).
% 5.95/2.21  tff(c_953, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_952])).
% 5.95/2.21  tff(c_956, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_56, c_953])).
% 5.95/2.21  tff(c_959, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_956])).
% 5.95/2.21  tff(c_961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_959])).
% 5.95/2.21  tff(c_963, plain, (l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_952])).
% 5.95/2.21  tff(c_962, plain, (v2_struct_0('#skF_6'('#skF_7')) | k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_952])).
% 5.95/2.21  tff(c_964, plain, (k10_yellow_6('#skF_7', '#skF_6'('#skF_7'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_962])).
% 5.95/2.21  tff(c_1011, plain, (![C_106]: (r3_waybel_9('#skF_7', '#skF_6'('#skF_7'), C_106) | ~r2_hidden(C_106, k1_xboole_0) | ~m1_subset_1(C_106, u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_964, c_46])).
% 5.95/2.21  tff(c_1073, plain, (![C_106]: (r3_waybel_9('#skF_7', '#skF_6'('#skF_7'), C_106) | ~r2_hidden(C_106, k1_xboole_0) | ~m1_subset_1(C_106, u1_struct_0('#skF_7')) | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_843, c_915, c_963, c_1011])).
% 5.95/2.21  tff(c_1074, plain, (![C_106]: (r3_waybel_9('#skF_7', '#skF_6'('#skF_7'), C_106) | ~r2_hidden(C_106, k1_xboole_0) | ~m1_subset_1(C_106, u1_struct_0('#skF_7')) | v2_struct_0('#skF_6'('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1073])).
% 5.95/2.21  tff(c_1086, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_1074])).
% 5.95/2.21  tff(c_62, plain, (![A_136]: (~v2_struct_0('#skF_6'(A_136)) | v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_1090, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1086, c_62])).
% 5.95/2.21  tff(c_1093, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1090])).
% 5.95/2.21  tff(c_1095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_1093])).
% 5.95/2.21  tff(c_1097, plain, (~v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1074])).
% 5.95/2.21  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.95/2.21  tff(c_130, plain, (![C_173, A_174, B_175]: (~v2_struct_0(C_173) | ~m2_yellow_6(C_173, A_174, B_175) | ~l1_waybel_0(B_175, A_174) | ~v7_waybel_0(B_175) | ~v4_orders_2(B_175) | v2_struct_0(B_175) | ~l1_struct_0(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_133, plain, (![B_155]: (~v2_struct_0('#skF_9'(B_155)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(resolution, [status(thm)], [c_127, c_130])).
% 5.95/2.21  tff(c_136, plain, (![B_155]: (~v2_struct_0('#skF_9'(B_155)) | ~l1_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(negUnitSimplification, [status(thm)], [c_72, c_133])).
% 5.95/2.21  tff(c_137, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_136])).
% 5.95/2.21  tff(c_140, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_10, c_137])).
% 5.95/2.21  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_140])).
% 5.95/2.21  tff(c_146, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_136])).
% 5.95/2.21  tff(c_157, plain, (![C_181, A_182, B_183]: (v7_waybel_0(C_181) | ~m2_yellow_6(C_181, A_182, B_183) | ~l1_waybel_0(B_183, A_182) | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_160, plain, (![B_155]: (v7_waybel_0('#skF_9'(B_155)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(resolution, [status(thm)], [c_127, c_157])).
% 5.95/2.21  tff(c_163, plain, (![B_155]: (v7_waybel_0('#skF_9'(B_155)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_160])).
% 5.95/2.21  tff(c_164, plain, (![B_155]: (v7_waybel_0('#skF_9'(B_155)) | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(negUnitSimplification, [status(thm)], [c_72, c_163])).
% 5.95/2.21  tff(c_166, plain, (![C_185, A_186, B_187]: (l1_waybel_0(C_185, A_186) | ~m2_yellow_6(C_185, A_186, B_187) | ~l1_waybel_0(B_187, A_186) | ~v7_waybel_0(B_187) | ~v4_orders_2(B_187) | v2_struct_0(B_187) | ~l1_struct_0(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_169, plain, (![B_155]: (l1_waybel_0('#skF_9'(B_155), '#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(resolution, [status(thm)], [c_127, c_166])).
% 5.95/2.21  tff(c_172, plain, (![B_155]: (l1_waybel_0('#skF_9'(B_155), '#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_169])).
% 5.95/2.21  tff(c_173, plain, (![B_155]: (l1_waybel_0('#skF_9'(B_155), '#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(negUnitSimplification, [status(thm)], [c_72, c_172])).
% 5.95/2.21  tff(c_147, plain, (![C_176, A_177, B_178]: (v4_orders_2(C_176) | ~m2_yellow_6(C_176, A_177, B_178) | ~l1_waybel_0(B_178, A_177) | ~v7_waybel_0(B_178) | ~v4_orders_2(B_178) | v2_struct_0(B_178) | ~l1_struct_0(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_150, plain, (![B_155]: (v4_orders_2('#skF_9'(B_155)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(resolution, [status(thm)], [c_127, c_147])).
% 5.95/2.21  tff(c_153, plain, (![B_155]: (v4_orders_2('#skF_9'(B_155)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_150])).
% 5.95/2.21  tff(c_154, plain, (![B_155]: (v4_orders_2('#skF_9'(B_155)) | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(negUnitSimplification, [status(thm)], [c_72, c_153])).
% 5.95/2.21  tff(c_859, plain, (~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_842])).
% 5.95/2.21  tff(c_1273, plain, (~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_963, c_859])).
% 5.95/2.21  tff(c_1274, plain, (~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_1097, c_1273])).
% 5.95/2.21  tff(c_1275, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7')))), inference(splitLeft, [status(thm)], [c_1274])).
% 5.95/2.21  tff(c_1278, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_154, c_1275])).
% 5.95/2.21  tff(c_1281, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_915, c_963, c_1278])).
% 5.95/2.21  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1281])).
% 5.95/2.21  tff(c_1284, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1274])).
% 5.95/2.21  tff(c_1286, plain, (~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7')), inference(splitLeft, [status(thm)], [c_1284])).
% 5.95/2.21  tff(c_1289, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_173, c_1286])).
% 5.95/2.21  tff(c_1292, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_915, c_963, c_1289])).
% 5.95/2.21  tff(c_1294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1292])).
% 5.95/2.21  tff(c_1295, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitRight, [status(thm)], [c_1284])).
% 5.95/2.21  tff(c_1298, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitLeft, [status(thm)], [c_1295])).
% 5.95/2.21  tff(c_1301, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_164, c_1298])).
% 5.95/2.21  tff(c_1304, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_915, c_963, c_1301])).
% 5.95/2.21  tff(c_1306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1304])).
% 5.95/2.21  tff(c_1307, plain, (v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1295])).
% 5.95/2.21  tff(c_1310, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1307])).
% 5.95/2.21  tff(c_96, plain, (![B_155]: (v1_compts_1('#skF_7') | v3_yellow_6('#skF_9'(B_155), '#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_123, plain, (![B_155]: (v3_yellow_6('#skF_9'(B_155), '#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(negUnitSimplification, [status(thm)], [c_110, c_96])).
% 5.95/2.21  tff(c_175, plain, (![A_189, B_190]: (k10_yellow_6(A_189, B_190)!=k1_xboole_0 | ~v3_yellow_6(B_190, A_189) | ~l1_waybel_0(B_190, A_189) | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.95/2.21  tff(c_178, plain, (![B_155]: (k10_yellow_6('#skF_7', '#skF_9'(B_155))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_155), '#skF_7') | ~v7_waybel_0('#skF_9'(B_155)) | ~v4_orders_2('#skF_9'(B_155)) | v2_struct_0('#skF_9'(B_155)) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(resolution, [status(thm)], [c_123, c_175])).
% 5.95/2.21  tff(c_181, plain, (![B_155]: (k10_yellow_6('#skF_7', '#skF_9'(B_155))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_155), '#skF_7') | ~v7_waybel_0('#skF_9'(B_155)) | ~v4_orders_2('#skF_9'(B_155)) | v2_struct_0('#skF_9'(B_155)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_178])).
% 5.95/2.21  tff(c_200, plain, (![B_199]: (k10_yellow_6('#skF_7', '#skF_9'(B_199))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_199), '#skF_7') | ~v7_waybel_0('#skF_9'(B_199)) | ~v4_orders_2('#skF_9'(B_199)) | v2_struct_0('#skF_9'(B_199)) | ~l1_waybel_0(B_199, '#skF_7') | ~v7_waybel_0(B_199) | ~v4_orders_2(B_199) | v2_struct_0(B_199))), inference(negUnitSimplification, [status(thm)], [c_72, c_181])).
% 5.95/2.21  tff(c_206, plain, (![B_202]: (k10_yellow_6('#skF_7', '#skF_9'(B_202))!=k1_xboole_0 | ~v7_waybel_0('#skF_9'(B_202)) | ~v4_orders_2('#skF_9'(B_202)) | v2_struct_0('#skF_9'(B_202)) | ~l1_waybel_0(B_202, '#skF_7') | ~v7_waybel_0(B_202) | ~v4_orders_2(B_202) | v2_struct_0(B_202))), inference(resolution, [status(thm)], [c_173, c_200])).
% 5.95/2.21  tff(c_211, plain, (![B_203]: (k10_yellow_6('#skF_7', '#skF_9'(B_203))!=k1_xboole_0 | ~v4_orders_2('#skF_9'(B_203)) | v2_struct_0('#skF_9'(B_203)) | ~l1_waybel_0(B_203, '#skF_7') | ~v7_waybel_0(B_203) | ~v4_orders_2(B_203) | v2_struct_0(B_203))), inference(resolution, [status(thm)], [c_164, c_206])).
% 5.95/2.21  tff(c_216, plain, (![B_204]: (k10_yellow_6('#skF_7', '#skF_9'(B_204))!=k1_xboole_0 | v2_struct_0('#skF_9'(B_204)) | ~l1_waybel_0(B_204, '#skF_7') | ~v7_waybel_0(B_204) | ~v4_orders_2(B_204) | v2_struct_0(B_204))), inference(resolution, [status(thm)], [c_154, c_211])).
% 5.95/2.21  tff(c_145, plain, (![B_155]: (~v2_struct_0('#skF_9'(B_155)) | ~l1_waybel_0(B_155, '#skF_7') | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155))), inference(splitRight, [status(thm)], [c_136])).
% 5.95/2.21  tff(c_220, plain, (![B_204]: (k10_yellow_6('#skF_7', '#skF_9'(B_204))!=k1_xboole_0 | ~l1_waybel_0(B_204, '#skF_7') | ~v7_waybel_0(B_204) | ~v4_orders_2(B_204) | v2_struct_0(B_204))), inference(resolution, [status(thm)], [c_216, c_145])).
% 5.95/2.21  tff(c_1361, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1310, c_220])).
% 5.95/2.21  tff(c_1426, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_915, c_963, c_1361])).
% 5.95/2.21  tff(c_1428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1426])).
% 5.95/2.21  tff(c_1429, plain, (v2_struct_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitRight, [status(thm)], [c_1307])).
% 5.95/2.21  tff(c_1433, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_1429, c_145])).
% 5.95/2.21  tff(c_1436, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_915, c_963, c_1433])).
% 5.95/2.21  tff(c_1438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1436])).
% 5.95/2.21  tff(c_1439, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 5.95/2.21  tff(c_1440, plain, (v1_compts_1('#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 5.95/2.21  tff(c_80, plain, (v4_orders_2('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_1445, plain, (v4_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_80])).
% 5.95/2.21  tff(c_78, plain, (v7_waybel_0('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_1442, plain, (v7_waybel_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_78])).
% 5.95/2.21  tff(c_76, plain, (l1_waybel_0('#skF_8', '#skF_7') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_1447, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_76])).
% 5.95/2.21  tff(c_64, plain, (![A_136, B_143]: (r3_waybel_9(A_136, B_143, '#skF_5'(A_136, B_143)) | ~l1_waybel_0(B_143, A_136) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_66, plain, (![A_136, B_143]: (m1_subset_1('#skF_5'(A_136, B_143), u1_struct_0(A_136)) | ~l1_waybel_0(B_143, A_136) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.95/2.21  tff(c_1495, plain, (![A_504, B_505, C_506]: (m2_yellow_6('#skF_4'(A_504, B_505, C_506), A_504, B_505) | ~r3_waybel_9(A_504, B_505, C_506) | ~m1_subset_1(C_506, u1_struct_0(A_504)) | ~l1_waybel_0(B_505, A_504) | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(cnfTransformation, [status(thm)], [f_218])).
% 5.95/2.21  tff(c_34, plain, (![C_96, A_93, B_94]: (l1_waybel_0(C_96, A_93) | ~m2_yellow_6(C_96, A_93, B_94) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_1574, plain, (![A_528, B_529, C_530]: (l1_waybel_0('#skF_4'(A_528, B_529, C_530), A_528) | ~l1_struct_0(A_528) | ~r3_waybel_9(A_528, B_529, C_530) | ~m1_subset_1(C_530, u1_struct_0(A_528)) | ~l1_waybel_0(B_529, A_528) | ~v7_waybel_0(B_529) | ~v4_orders_2(B_529) | v2_struct_0(B_529) | ~l1_pre_topc(A_528) | ~v2_pre_topc(A_528) | v2_struct_0(A_528))), inference(resolution, [status(thm)], [c_1495, c_34])).
% 5.95/2.21  tff(c_1639, plain, (![A_578, B_579, B_580]: (l1_waybel_0('#skF_4'(A_578, B_579, '#skF_5'(A_578, B_580)), A_578) | ~l1_struct_0(A_578) | ~r3_waybel_9(A_578, B_579, '#skF_5'(A_578, B_580)) | ~l1_waybel_0(B_579, A_578) | ~v7_waybel_0(B_579) | ~v4_orders_2(B_579) | v2_struct_0(B_579) | ~l1_waybel_0(B_580, A_578) | ~v7_waybel_0(B_580) | ~v4_orders_2(B_580) | v2_struct_0(B_580) | ~v1_compts_1(A_578) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | v2_struct_0(A_578))), inference(resolution, [status(thm)], [c_66, c_1574])).
% 5.95/2.21  tff(c_42, plain, (![B_99, A_97]: (v3_yellow_6(B_99, A_97) | k10_yellow_6(A_97, B_99)=k1_xboole_0 | ~l1_waybel_0(B_99, A_97) | ~v7_waybel_0(B_99) | ~v4_orders_2(B_99) | v2_struct_0(B_99) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.95/2.21  tff(c_74, plain, (![C_154]: (~v3_yellow_6(C_154, '#skF_7') | ~m2_yellow_6(C_154, '#skF_7', '#skF_8') | ~v1_compts_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.95/2.21  tff(c_1456, plain, (![C_154]: (~v3_yellow_6(C_154, '#skF_7') | ~m2_yellow_6(C_154, '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_74])).
% 5.95/2.21  tff(c_1511, plain, (![C_506]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_506), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_506) | ~m1_subset_1(C_506, u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1495, c_1456])).
% 5.95/2.21  tff(c_1518, plain, (![C_506]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_506), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_506) | ~m1_subset_1(C_506, u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1445, c_1442, c_1447, c_1511])).
% 5.95/2.21  tff(c_1520, plain, (![C_507]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_507), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_507) | ~m1_subset_1(C_507, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1518])).
% 5.95/2.21  tff(c_1523, plain, (![C_507]: (~r3_waybel_9('#skF_7', '#skF_8', C_507) | ~m1_subset_1(C_507, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_507))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_507), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_507)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_507)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_507)) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1520])).
% 5.95/2.21  tff(c_1526, plain, (![C_507]: (~r3_waybel_9('#skF_7', '#skF_8', C_507) | ~m1_subset_1(C_507, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_507))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_507), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_507)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_507)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_507)) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1523])).
% 5.95/2.21  tff(c_1548, plain, (![C_524]: (~r3_waybel_9('#skF_7', '#skF_8', C_524) | ~m1_subset_1(C_524, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_524))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_524), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_524)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_524)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_524)))), inference(negUnitSimplification, [status(thm)], [c_72, c_1526])).
% 5.95/2.21  tff(c_1556, plain, (![B_143]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1548])).
% 5.95/2.21  tff(c_1563, plain, (![B_143]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1556])).
% 5.95/2.21  tff(c_1564, plain, (![B_143]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143))), inference(negUnitSimplification, [status(thm)], [c_72, c_1563])).
% 5.95/2.21  tff(c_1643, plain, (![B_580]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_580, '#skF_7') | ~v7_waybel_0(B_580) | ~v4_orders_2(B_580) | v2_struct_0(B_580) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1639, c_1564])).
% 5.95/2.21  tff(c_1646, plain, (![B_580]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_580, '#skF_7') | ~v7_waybel_0(B_580) | ~v4_orders_2(B_580) | v2_struct_0(B_580) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1445, c_1442, c_1447, c_1643])).
% 5.95/2.21  tff(c_1647, plain, (![B_580]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_580)) | ~l1_waybel_0(B_580, '#skF_7') | ~v7_waybel_0(B_580) | ~v4_orders_2(B_580) | v2_struct_0(B_580))), inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1646])).
% 5.95/2.21  tff(c_1648, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1647])).
% 5.95/2.21  tff(c_1651, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_10, c_1648])).
% 5.95/2.21  tff(c_1655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1651])).
% 5.95/2.21  tff(c_1657, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1647])).
% 5.95/2.21  tff(c_38, plain, (![C_96, A_93, B_94]: (v4_orders_2(C_96) | ~m2_yellow_6(C_96, A_93, B_94) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_1528, plain, (![A_508, B_509, C_510]: (v4_orders_2('#skF_4'(A_508, B_509, C_510)) | ~l1_struct_0(A_508) | ~r3_waybel_9(A_508, B_509, C_510) | ~m1_subset_1(C_510, u1_struct_0(A_508)) | ~l1_waybel_0(B_509, A_508) | ~v7_waybel_0(B_509) | ~v4_orders_2(B_509) | v2_struct_0(B_509) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(resolution, [status(thm)], [c_1495, c_38])).
% 5.95/2.21  tff(c_1531, plain, (![A_136, B_509, B_143]: (v4_orders_2('#skF_4'(A_136, B_509, '#skF_5'(A_136, B_143))) | ~l1_struct_0(A_136) | ~r3_waybel_9(A_136, B_509, '#skF_5'(A_136, B_143)) | ~l1_waybel_0(B_509, A_136) | ~v7_waybel_0(B_509) | ~v4_orders_2(B_509) | v2_struct_0(B_509) | ~l1_waybel_0(B_143, A_136) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_66, c_1528])).
% 5.95/2.21  tff(c_36, plain, (![C_96, A_93, B_94]: (v7_waybel_0(C_96) | ~m2_yellow_6(C_96, A_93, B_94) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_1537, plain, (![A_517, B_518, C_519]: (v7_waybel_0('#skF_4'(A_517, B_518, C_519)) | ~l1_struct_0(A_517) | ~r3_waybel_9(A_517, B_518, C_519) | ~m1_subset_1(C_519, u1_struct_0(A_517)) | ~l1_waybel_0(B_518, A_517) | ~v7_waybel_0(B_518) | ~v4_orders_2(B_518) | v2_struct_0(B_518) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(resolution, [status(thm)], [c_1495, c_36])).
% 5.95/2.21  tff(c_1543, plain, (![A_136, B_518, B_143]: (v7_waybel_0('#skF_4'(A_136, B_518, '#skF_5'(A_136, B_143))) | ~l1_struct_0(A_136) | ~r3_waybel_9(A_136, B_518, '#skF_5'(A_136, B_143)) | ~l1_waybel_0(B_518, A_136) | ~v7_waybel_0(B_518) | ~v4_orders_2(B_518) | v2_struct_0(B_518) | ~l1_waybel_0(B_143, A_136) | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1(A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_66, c_1537])).
% 5.95/2.21  tff(c_1658, plain, (![B_581]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_581)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_581))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_581))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_581))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_581)) | ~l1_waybel_0(B_581, '#skF_7') | ~v7_waybel_0(B_581) | ~v4_orders_2(B_581) | v2_struct_0(B_581))), inference(splitRight, [status(thm)], [c_1647])).
% 5.95/2.21  tff(c_1662, plain, (![B_143]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1543, c_1658])).
% 5.95/2.21  tff(c_1665, plain, (![B_143]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1445, c_1442, c_1447, c_1657, c_1662])).
% 5.95/2.21  tff(c_1667, plain, (![B_582]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_582)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_582))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_582))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_582)) | ~l1_waybel_0(B_582, '#skF_7') | ~v7_waybel_0(B_582) | ~v4_orders_2(B_582) | v2_struct_0(B_582))), inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1665])).
% 5.95/2.21  tff(c_1671, plain, (![B_143]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1531, c_1667])).
% 5.95/2.21  tff(c_1674, plain, (![B_143]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1445, c_1442, c_1447, c_1657, c_1671])).
% 5.95/2.21  tff(c_1676, plain, (![B_583]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583)) | ~l1_waybel_0(B_583, '#skF_7') | ~v7_waybel_0(B_583) | ~v4_orders_2(B_583) | v2_struct_0(B_583))), inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1674])).
% 5.95/2.21  tff(c_40, plain, (![C_96, A_93, B_94]: (~v2_struct_0(C_96) | ~m2_yellow_6(C_96, A_93, B_94) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.95/2.21  tff(c_1514, plain, (![A_504, B_505, C_506]: (~v2_struct_0('#skF_4'(A_504, B_505, C_506)) | ~l1_struct_0(A_504) | ~r3_waybel_9(A_504, B_505, C_506) | ~m1_subset_1(C_506, u1_struct_0(A_504)) | ~l1_waybel_0(B_505, A_504) | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(resolution, [status(thm)], [c_1495, c_40])).
% 5.95/2.21  tff(c_1678, plain, (![B_583]: (~l1_struct_0('#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', B_583), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583)) | ~l1_waybel_0(B_583, '#skF_7') | ~v7_waybel_0(B_583) | ~v4_orders_2(B_583) | v2_struct_0(B_583))), inference(resolution, [status(thm)], [c_1676, c_1514])).
% 5.95/2.21  tff(c_1681, plain, (![B_583]: (~m1_subset_1('#skF_5'('#skF_7', B_583), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7') | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_583)) | ~l1_waybel_0(B_583, '#skF_7') | ~v7_waybel_0(B_583) | ~v4_orders_2(B_583) | v2_struct_0(B_583))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1445, c_1442, c_1447, c_1657, c_1678])).
% 5.95/2.21  tff(c_1687, plain, (![B_587]: (~m1_subset_1('#skF_5'('#skF_7', B_587), u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_587)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_587)) | ~l1_waybel_0(B_587, '#skF_7') | ~v7_waybel_0(B_587) | ~v4_orders_2(B_587) | v2_struct_0(B_587))), inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1681])).
% 5.95/2.21  tff(c_1691, plain, (![B_143]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1687])).
% 5.95/2.21  tff(c_1694, plain, (![B_143]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1691])).
% 5.95/2.21  tff(c_1696, plain, (![B_588]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_588)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_588)) | ~l1_waybel_0(B_588, '#skF_7') | ~v7_waybel_0(B_588) | ~v4_orders_2(B_588) | v2_struct_0(B_588))), inference(negUnitSimplification, [status(thm)], [c_72, c_1694])).
% 5.95/2.21  tff(c_1565, plain, (![C_525, A_526, B_527]: (r2_hidden(C_525, k10_yellow_6(A_526, '#skF_4'(A_526, B_527, C_525))) | ~r3_waybel_9(A_526, B_527, C_525) | ~m1_subset_1(C_525, u1_struct_0(A_526)) | ~l1_waybel_0(B_527, A_526) | ~v7_waybel_0(B_527) | ~v4_orders_2(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_526) | ~v2_pre_topc(A_526) | v2_struct_0(A_526))), inference(cnfTransformation, [status(thm)], [f_218])).
% 5.95/2.21  tff(c_1573, plain, (![A_526, B_527, C_525]: (~r1_tarski(k10_yellow_6(A_526, '#skF_4'(A_526, B_527, C_525)), C_525) | ~r3_waybel_9(A_526, B_527, C_525) | ~m1_subset_1(C_525, u1_struct_0(A_526)) | ~l1_waybel_0(B_527, A_526) | ~v7_waybel_0(B_527) | ~v4_orders_2(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_526) | ~v2_pre_topc(A_526) | v2_struct_0(A_526))), inference(resolution, [status(thm)], [c_1565, c_8])).
% 5.95/2.21  tff(c_1707, plain, (![B_588]: (~r1_tarski(k1_xboole_0, '#skF_5'('#skF_7', B_588)) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_588)) | ~m1_subset_1('#skF_5'('#skF_7', B_588), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_588)) | ~l1_waybel_0(B_588, '#skF_7') | ~v7_waybel_0(B_588) | ~v4_orders_2(B_588) | v2_struct_0(B_588))), inference(superposition, [status(thm), theory('equality')], [c_1696, c_1573])).
% 5.95/2.21  tff(c_1731, plain, (![B_588]: (~m1_subset_1('#skF_5'('#skF_7', B_588), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_588)) | ~l1_waybel_0(B_588, '#skF_7') | ~v7_waybel_0(B_588) | ~v4_orders_2(B_588) | v2_struct_0(B_588))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1445, c_1442, c_1447, c_2, c_1707])).
% 5.95/2.21  tff(c_1746, plain, (![B_589]: (~m1_subset_1('#skF_5'('#skF_7', B_589), u1_struct_0('#skF_7')) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_589)) | ~l1_waybel_0(B_589, '#skF_7') | ~v7_waybel_0(B_589) | ~v4_orders_2(B_589) | v2_struct_0(B_589))), inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1731])).
% 5.95/2.21  tff(c_1750, plain, (![B_143]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1746])).
% 5.95/2.21  tff(c_1753, plain, (![B_143]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_143)) | ~l1_waybel_0(B_143, '#skF_7') | ~v7_waybel_0(B_143) | ~v4_orders_2(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1750])).
% 5.95/2.21  tff(c_1755, plain, (![B_590]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_590)) | ~l1_waybel_0(B_590, '#skF_7') | ~v7_waybel_0(B_590) | ~v4_orders_2(B_590) | v2_struct_0(B_590))), inference(negUnitSimplification, [status(thm)], [c_72, c_1753])).
% 5.95/2.21  tff(c_1763, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_64, c_1755])).
% 5.95/2.21  tff(c_1770, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1440, c_1445, c_1442, c_1447, c_1763])).
% 5.95/2.21  tff(c_1772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1439, c_1770])).
% 5.95/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.21  
% 5.95/2.21  Inference rules
% 5.95/2.21  ----------------------
% 5.95/2.21  #Ref     : 0
% 5.95/2.21  #Sup     : 303
% 5.95/2.21  #Fact    : 2
% 5.95/2.21  #Define  : 0
% 5.95/2.21  #Split   : 16
% 5.95/2.21  #Chain   : 0
% 5.95/2.21  #Close   : 0
% 5.95/2.21  
% 5.95/2.21  Ordering : KBO
% 5.95/2.21  
% 5.95/2.21  Simplification rules
% 5.95/2.21  ----------------------
% 5.95/2.21  #Subsume      : 83
% 5.95/2.21  #Demod        : 515
% 5.95/2.21  #Tautology    : 50
% 5.95/2.21  #SimpNegUnit  : 106
% 5.95/2.21  #BackRed      : 0
% 5.95/2.21  
% 5.95/2.21  #Partial instantiations: 0
% 5.95/2.21  #Strategies tried      : 1
% 5.95/2.21  
% 5.95/2.21  Timing (in seconds)
% 5.95/2.21  ----------------------
% 5.95/2.21  Preprocessing        : 0.40
% 5.95/2.21  Parsing              : 0.22
% 5.95/2.21  CNF conversion       : 0.04
% 5.95/2.21  Main loop            : 0.93
% 5.95/2.21  Inferencing          : 0.37
% 5.95/2.21  Reduction            : 0.24
% 5.95/2.21  Demodulation         : 0.15
% 5.95/2.21  BG Simplification    : 0.05
% 5.95/2.21  Subsumption          : 0.22
% 5.95/2.21  Abstraction          : 0.04
% 5.95/2.21  MUC search           : 0.00
% 5.95/2.21  Cooper               : 0.00
% 5.95/2.21  Total                : 1.41
% 5.95/2.21  Index Insertion      : 0.00
% 5.95/2.21  Index Deletion       : 0.00
% 5.95/2.21  Index Matching       : 0.00
% 5.95/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
