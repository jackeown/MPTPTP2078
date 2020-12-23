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
% DateTime   : Thu Dec  3 10:31:40 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  239 (3031 expanded)
%              Number of leaves         :   42 ( 999 expanded)
%              Depth                    :   37
%              Number of atoms          : 1156 (19142 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_250,negated_conjecture,(
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

tff(f_225,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_72,plain,
    ( ~ v2_struct_0('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_102,plain,(
    ~ v1_compts_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_50,plain,(
    ! [A_60] :
      ( v4_orders_2('#skF_4'(A_60))
      | v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_98,plain,(
    ! [B_79] :
      ( v1_compts_1('#skF_5')
      | m2_yellow_6('#skF_7'(B_79),'#skF_5',B_79)
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_202,plain,(
    ! [B_79] :
      ( m2_yellow_6('#skF_7'(B_79),'#skF_5',B_79)
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_98])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_250,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1(k10_yellow_6(A_137,B_138),k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_waybel_0(B_138,A_137)
      | ~ v7_waybel_0(B_138)
      | ~ v4_orders_2(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_274,plain,(
    ! [A_147,A_148,B_149] :
      ( m1_subset_1(A_147,u1_struct_0(A_148))
      | ~ r2_hidden(A_147,k10_yellow_6(A_148,B_149))
      | ~ l1_waybel_0(B_149,A_148)
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_250,c_16])).

tff(c_284,plain,(
    ! [A_148,B_149,B_2] :
      ( m1_subset_1('#skF_1'(k10_yellow_6(A_148,B_149),B_2),u1_struct_0(A_148))
      | ~ l1_waybel_0(B_149,A_148)
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148)
      | r1_tarski(k10_yellow_6(A_148,B_149),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_306,plain,(
    ! [A_155,B_156,C_157] :
      ( r3_waybel_9(A_155,B_156,C_157)
      | ~ r2_hidden(C_157,k10_yellow_6(A_155,B_156))
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ l1_waybel_0(B_156,A_155)
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_398,plain,(
    ! [A_198,B_199,B_200] :
      ( r3_waybel_9(A_198,B_199,'#skF_1'(k10_yellow_6(A_198,B_199),B_200))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_198,B_199),B_200),u1_struct_0(A_198))
      | ~ l1_waybel_0(B_199,A_198)
      | ~ v7_waybel_0(B_199)
      | ~ v4_orders_2(B_199)
      | v2_struct_0(B_199)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198)
      | r1_tarski(k10_yellow_6(A_198,B_199),B_200) ) ),
    inference(resolution,[status(thm)],[c_6,c_306])).

tff(c_402,plain,(
    ! [A_201,B_202,B_203] :
      ( r3_waybel_9(A_201,B_202,'#skF_1'(k10_yellow_6(A_201,B_202),B_203))
      | ~ l1_waybel_0(B_202,A_201)
      | ~ v7_waybel_0(B_202)
      | ~ v4_orders_2(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201)
      | r1_tarski(k10_yellow_6(A_201,B_202),B_203) ) ),
    inference(resolution,[status(thm)],[c_284,c_398])).

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

tff(c_679,plain,(
    ! [A_267,B_268,B_269,B_270] :
      ( r3_waybel_9(A_267,B_268,'#skF_1'(k10_yellow_6(A_267,B_269),B_270))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_267,B_269),B_270),u1_struct_0(A_267))
      | ~ m2_yellow_6(B_269,A_267,B_268)
      | ~ l1_waybel_0(B_268,A_267)
      | ~ v7_waybel_0(B_268)
      | ~ v4_orders_2(B_268)
      | v2_struct_0(B_268)
      | ~ l1_waybel_0(B_269,A_267)
      | ~ v7_waybel_0(B_269)
      | ~ v4_orders_2(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267)
      | r1_tarski(k10_yellow_6(A_267,B_269),B_270) ) ),
    inference(resolution,[status(thm)],[c_402,c_38])).

tff(c_689,plain,(
    ! [A_275,B_276,B_277,B_278] :
      ( r3_waybel_9(A_275,B_276,'#skF_1'(k10_yellow_6(A_275,B_277),B_278))
      | ~ m2_yellow_6(B_277,A_275,B_276)
      | ~ l1_waybel_0(B_276,A_275)
      | ~ v7_waybel_0(B_276)
      | ~ v4_orders_2(B_276)
      | v2_struct_0(B_276)
      | ~ l1_waybel_0(B_277,A_275)
      | ~ v7_waybel_0(B_277)
      | ~ v4_orders_2(B_277)
      | v2_struct_0(B_277)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275)
      | r1_tarski(k10_yellow_6(A_275,B_277),B_278) ) ),
    inference(resolution,[status(thm)],[c_284,c_679])).

tff(c_44,plain,(
    ! [A_60,C_70] :
      ( ~ r3_waybel_9(A_60,'#skF_4'(A_60),C_70)
      | ~ m1_subset_1(C_70,u1_struct_0(A_60))
      | v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_701,plain,(
    ! [A_279,B_280,B_281] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6(A_279,B_280),B_281),u1_struct_0(A_279))
      | v1_compts_1(A_279)
      | ~ m2_yellow_6(B_280,A_279,'#skF_4'(A_279))
      | ~ l1_waybel_0('#skF_4'(A_279),A_279)
      | ~ v7_waybel_0('#skF_4'(A_279))
      | ~ v4_orders_2('#skF_4'(A_279))
      | v2_struct_0('#skF_4'(A_279))
      | ~ l1_waybel_0(B_280,A_279)
      | ~ v7_waybel_0(B_280)
      | ~ v4_orders_2(B_280)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279)
      | r1_tarski(k10_yellow_6(A_279,B_280),B_281) ) ),
    inference(resolution,[status(thm)],[c_689,c_44])).

tff(c_709,plain,(
    ! [A_282,B_283,B_284] :
      ( v1_compts_1(A_282)
      | ~ m2_yellow_6(B_283,A_282,'#skF_4'(A_282))
      | ~ l1_waybel_0('#skF_4'(A_282),A_282)
      | ~ v7_waybel_0('#skF_4'(A_282))
      | ~ v4_orders_2('#skF_4'(A_282))
      | v2_struct_0('#skF_4'(A_282))
      | ~ l1_waybel_0(B_283,A_282)
      | ~ v7_waybel_0(B_283)
      | ~ v4_orders_2(B_283)
      | v2_struct_0(B_283)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282)
      | r1_tarski(k10_yellow_6(A_282,B_283),B_284) ) ),
    inference(resolution,[status(thm)],[c_284,c_701])).

tff(c_715,plain,(
    ! [B_284] :
      ( v1_compts_1('#skF_5')
      | ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
      | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
      | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284)
      | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | ~ v7_waybel_0('#skF_4'('#skF_5'))
      | ~ v4_orders_2('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_4'('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_202,c_709])).

tff(c_719,plain,(
    ! [B_284] :
      ( v1_compts_1('#skF_5')
      | ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
      | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
      | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_5')
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284)
      | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | ~ v7_waybel_0('#skF_4'('#skF_5'))
      | ~ v4_orders_2('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_4'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_715])).

tff(c_720,plain,(
    ! [B_284] :
      ( ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
      | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
      | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284)
      | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | ~ v7_waybel_0('#skF_4'('#skF_5'))
      | ~ v4_orders_2('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_4'('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_719])).

tff(c_721,plain,(
    ~ v4_orders_2('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_720])).

tff(c_724,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_721])).

tff(c_727,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_724])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_727])).

tff(c_731,plain,(
    v4_orders_2('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_48,plain,(
    ! [A_60] :
      ( v7_waybel_0('#skF_4'(A_60))
      | v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_46,plain,(
    ! [A_60] :
      ( l1_waybel_0('#skF_4'(A_60),A_60)
      | v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [C_121,A_122,B_123] :
      ( v4_orders_2(C_121)
      | ~ m2_yellow_6(C_121,A_122,B_123)
      | ~ l1_waybel_0(B_123,A_122)
      | ~ v7_waybel_0(B_123)
      | ~ v4_orders_2(B_123)
      | v2_struct_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_208,plain,(
    ! [B_79] :
      ( v4_orders_2('#skF_7'(B_79))
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_202,c_205])).

tff(c_211,plain,(
    ! [B_79] :
      ( v4_orders_2('#skF_7'(B_79))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_208])).

tff(c_212,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_215,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_215])).

tff(c_221,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_241,plain,(
    ! [C_133,A_134,B_135] :
      ( l1_waybel_0(C_133,A_134)
      | ~ m2_yellow_6(C_133,A_134,B_135)
      | ~ l1_waybel_0(B_135,A_134)
      | ~ v7_waybel_0(B_135)
      | ~ v4_orders_2(B_135)
      | v2_struct_0(B_135)
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_244,plain,(
    ! [B_79] :
      ( l1_waybel_0('#skF_7'(B_79),'#skF_5')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_202,c_241])).

tff(c_247,plain,(
    ! [B_79] :
      ( l1_waybel_0('#skF_7'(B_79),'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_244])).

tff(c_248,plain,(
    ! [B_79] :
      ( l1_waybel_0('#skF_7'(B_79),'#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_247])).

tff(c_730,plain,(
    ! [B_284] :
      ( ~ v7_waybel_0('#skF_4'('#skF_5'))
      | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
      | ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
      | v2_struct_0('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_742,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_745,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_248,c_742])).

tff(c_748,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_745])).

tff(c_749,plain,(
    ~ v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_752,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_749])).

tff(c_755,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_752])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_755])).

tff(c_758,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_760,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_758])).

tff(c_763,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_760])).

tff(c_766,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_763])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_766])).

tff(c_769,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_758])).

tff(c_52,plain,(
    ! [A_60] :
      ( ~ v2_struct_0('#skF_4'(A_60))
      | v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_773,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_769,c_52])).

tff(c_776,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_773])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_776])).

tff(c_779,plain,(
    ! [B_284] :
      ( ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
      | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | ~ v7_waybel_0('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_4'('#skF_5'))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_787,plain,(
    ~ v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_790,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_787])).

tff(c_793,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_790])).

tff(c_795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_793])).

tff(c_797,plain,(
    v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_223,plain,(
    ! [C_125,A_126,B_127] :
      ( v7_waybel_0(C_125)
      | ~ m2_yellow_6(C_125,A_126,B_127)
      | ~ l1_waybel_0(B_127,A_126)
      | ~ v7_waybel_0(B_127)
      | ~ v4_orders_2(B_127)
      | v2_struct_0(B_127)
      | ~ l1_struct_0(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_226,plain,(
    ! [B_79] :
      ( v7_waybel_0('#skF_7'(B_79))
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_202,c_223])).

tff(c_229,plain,(
    ! [B_79] :
      ( v7_waybel_0('#skF_7'(B_79))
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_226])).

tff(c_230,plain,(
    ! [B_79] :
      ( v7_waybel_0('#skF_7'(B_79))
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_229])).

tff(c_796,plain,(
    ! [B_284] :
      ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_798,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_801,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_230,c_798])).

tff(c_804,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_797,c_801])).

tff(c_805,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_804])).

tff(c_808,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_805])).

tff(c_811,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_808])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_811])).

tff(c_814,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_804])).

tff(c_818,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_814,c_52])).

tff(c_821,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_818])).

tff(c_823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_821])).

tff(c_824,plain,(
    ! [B_284] :
      ( ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_4'('#skF_5'))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_836,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_839,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_836])).

tff(c_842,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_839])).

tff(c_844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_842])).

tff(c_846,plain,(
    l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_220,plain,(
    ! [B_79] :
      ( v4_orders_2('#skF_7'(B_79))
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_845,plain,(
    ! [B_284] :
      ( ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_4'('#skF_5'))
      | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_865,plain,(
    ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_845])).

tff(c_868,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_220,c_865])).

tff(c_871,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_797,c_846,c_868])).

tff(c_874,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_871,c_52])).

tff(c_877,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_874])).

tff(c_879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_877])).

tff(c_880,plain,(
    ! [B_284] :
      ( v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | v2_struct_0('#skF_4'('#skF_5'))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_845])).

tff(c_894,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_880])).

tff(c_897,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_894,c_52])).

tff(c_900,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_897])).

tff(c_902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102,c_900])).

tff(c_904,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_903,plain,(
    ! [B_284] :
      ( v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_284) ) ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_929,plain,(
    v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_903])).

tff(c_232,plain,(
    ! [C_129,A_130,B_131] :
      ( ~ v2_struct_0(C_129)
      | ~ m2_yellow_6(C_129,A_130,B_131)
      | ~ l1_waybel_0(B_131,A_130)
      | ~ v7_waybel_0(B_131)
      | ~ v4_orders_2(B_131)
      | v2_struct_0(B_131)
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_235,plain,(
    ! [B_79] :
      ( ~ v2_struct_0('#skF_7'(B_79))
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_202,c_232])).

tff(c_238,plain,(
    ! [B_79] :
      ( ~ v2_struct_0('#skF_7'(B_79))
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_235])).

tff(c_239,plain,(
    ! [B_79] :
      ( ~ v2_struct_0('#skF_7'(B_79))
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_238])).

tff(c_932,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_929,c_239])).

tff(c_935,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_797,c_846,c_932])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_904,c_935])).

tff(c_940,plain,(
    ! [B_308] : r1_tarski(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))),B_308) ),
    inference(splitRight,[status(thm)],[c_903])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_117,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_992,plain,(
    k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_940,c_126])).

tff(c_86,plain,(
    ! [B_79] :
      ( v1_compts_1('#skF_5')
      | v3_yellow_6('#skF_7'(B_79),'#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_192,plain,(
    ! [B_79] :
      ( v3_yellow_6('#skF_7'(B_79),'#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_86])).

tff(c_254,plain,(
    ! [A_139,B_140] :
      ( k10_yellow_6(A_139,B_140) != k1_xboole_0
      | ~ v3_yellow_6(B_140,A_139)
      | ~ l1_waybel_0(B_140,A_139)
      | ~ v7_waybel_0(B_140)
      | ~ v4_orders_2(B_140)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_257,plain,(
    ! [B_79] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_79)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(B_79),'#skF_5')
      | ~ v7_waybel_0('#skF_7'(B_79))
      | ~ v4_orders_2('#skF_7'(B_79))
      | v2_struct_0('#skF_7'(B_79))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_192,c_254])).

tff(c_260,plain,(
    ! [B_79] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_79)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(B_79),'#skF_5')
      | ~ v7_waybel_0('#skF_7'(B_79))
      | ~ v4_orders_2('#skF_7'(B_79))
      | v2_struct_0('#skF_7'(B_79))
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_79,'#skF_5')
      | ~ v7_waybel_0(B_79)
      | ~ v4_orders_2(B_79)
      | v2_struct_0(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_257])).

tff(c_285,plain,(
    ! [B_150] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_150)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(B_150),'#skF_5')
      | ~ v7_waybel_0('#skF_7'(B_150))
      | ~ v4_orders_2('#skF_7'(B_150))
      | v2_struct_0('#skF_7'(B_150))
      | ~ l1_waybel_0(B_150,'#skF_5')
      | ~ v7_waybel_0(B_150)
      | ~ v4_orders_2(B_150)
      | v2_struct_0(B_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_260])).

tff(c_290,plain,(
    ! [B_151] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_151)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_7'(B_151))
      | ~ v4_orders_2('#skF_7'(B_151))
      | v2_struct_0('#skF_7'(B_151))
      | ~ l1_waybel_0(B_151,'#skF_5')
      | ~ v7_waybel_0(B_151)
      | ~ v4_orders_2(B_151)
      | v2_struct_0(B_151) ) ),
    inference(resolution,[status(thm)],[c_248,c_285])).

tff(c_295,plain,(
    ! [B_152] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_152)) != k1_xboole_0
      | ~ v4_orders_2('#skF_7'(B_152))
      | v2_struct_0('#skF_7'(B_152))
      | ~ l1_waybel_0(B_152,'#skF_5')
      | ~ v7_waybel_0(B_152)
      | ~ v4_orders_2(B_152)
      | v2_struct_0(B_152) ) ),
    inference(resolution,[status(thm)],[c_230,c_290])).

tff(c_300,plain,(
    ! [B_153] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_153)) != k1_xboole_0
      | v2_struct_0('#skF_7'(B_153))
      | ~ l1_waybel_0(B_153,'#skF_5')
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153) ) ),
    inference(resolution,[status(thm)],[c_220,c_295])).

tff(c_304,plain,(
    ! [B_153] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_153)) != k1_xboole_0
      | ~ l1_waybel_0(B_153,'#skF_5')
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153) ) ),
    inference(resolution,[status(thm)],[c_300,c_239])).

tff(c_1029,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_304])).

tff(c_1073,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_797,c_846,c_1029])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_904,c_1073])).

tff(c_1076,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1077,plain,(
    v1_compts_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,
    ( v4_orders_2('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1080,plain,(
    v4_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_70])).

tff(c_68,plain,
    ( v7_waybel_0('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1082,plain,(
    v7_waybel_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_68])).

tff(c_66,plain,
    ( l1_waybel_0('#skF_6','#skF_5')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1084,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_66])).

tff(c_54,plain,(
    ! [A_60,B_67] :
      ( r3_waybel_9(A_60,B_67,'#skF_3'(A_60,B_67))
      | ~ l1_waybel_0(B_67,A_60)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_56,plain,(
    ! [A_60,B_67] :
      ( m1_subset_1('#skF_3'(A_60,B_67),u1_struct_0(A_60))
      | ~ l1_waybel_0(B_67,A_60)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1245,plain,(
    ! [A_381,B_382,C_383] :
      ( m2_yellow_6('#skF_2'(A_381,B_382,C_383),A_381,B_382)
      | ~ r3_waybel_9(A_381,B_382,C_383)
      | ~ m1_subset_1(C_383,u1_struct_0(A_381))
      | ~ l1_waybel_0(B_382,A_381)
      | ~ v7_waybel_0(B_382)
      | ~ v4_orders_2(B_382)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
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

tff(c_1331,plain,(
    ! [A_405,B_406,C_407] :
      ( l1_waybel_0('#skF_2'(A_405,B_406,C_407),A_405)
      | ~ l1_struct_0(A_405)
      | ~ r3_waybel_9(A_405,B_406,C_407)
      | ~ m1_subset_1(C_407,u1_struct_0(A_405))
      | ~ l1_waybel_0(B_406,A_405)
      | ~ v7_waybel_0(B_406)
      | ~ v4_orders_2(B_406)
      | v2_struct_0(B_406)
      | ~ l1_pre_topc(A_405)
      | ~ v2_pre_topc(A_405)
      | v2_struct_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_1245,c_24])).

tff(c_1616,plain,(
    ! [A_465,B_466,B_467] :
      ( l1_waybel_0('#skF_2'(A_465,B_466,'#skF_3'(A_465,B_467)),A_465)
      | ~ l1_struct_0(A_465)
      | ~ r3_waybel_9(A_465,B_466,'#skF_3'(A_465,B_467))
      | ~ l1_waybel_0(B_466,A_465)
      | ~ v7_waybel_0(B_466)
      | ~ v4_orders_2(B_466)
      | v2_struct_0(B_466)
      | ~ l1_waybel_0(B_467,A_465)
      | ~ v7_waybel_0(B_467)
      | ~ v4_orders_2(B_467)
      | v2_struct_0(B_467)
      | ~ v1_compts_1(A_465)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_56,c_1331])).

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

tff(c_64,plain,(
    ! [C_78] :
      ( ~ v3_yellow_6(C_78,'#skF_5')
      | ~ m2_yellow_6(C_78,'#skF_5','#skF_6')
      | ~ v1_compts_1('#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1109,plain,(
    ! [C_78] :
      ( ~ v3_yellow_6(C_78,'#skF_5')
      | ~ m2_yellow_6(C_78,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_64])).

tff(c_1261,plain,(
    ! [C_383] :
      ( ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_383),'#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6',C_383)
      | ~ m1_subset_1(C_383,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1245,c_1109])).

tff(c_1268,plain,(
    ! [C_383] :
      ( ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_383),'#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6',C_383)
      | ~ m1_subset_1(C_383,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1080,c_1082,c_1084,c_1261])).

tff(c_1286,plain,(
    ! [C_387] :
      ( ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_387),'#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6',C_387)
      | ~ m1_subset_1(C_387,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1268])).

tff(c_1289,plain,(
    ! [C_387] :
      ( ~ r3_waybel_9('#skF_5','#skF_6',C_387)
      | ~ m1_subset_1(C_387,u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6',C_387)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_387),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_387))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_387))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_387))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_1286])).

tff(c_1292,plain,(
    ! [C_387] :
      ( ~ r3_waybel_9('#skF_5','#skF_6',C_387)
      | ~ m1_subset_1(C_387,u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6',C_387)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_387),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_387))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_387))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_387))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1289])).

tff(c_1302,plain,(
    ! [C_394] :
      ( ~ r3_waybel_9('#skF_5','#skF_6',C_394)
      | ~ m1_subset_1(C_394,u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6',C_394)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_394),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_394))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_394))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_394)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1292])).

tff(c_1310,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1302])).

tff(c_1317,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1310])).

tff(c_1318,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1317])).

tff(c_1620,plain,(
    ! [B_467] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_467))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_467,'#skF_5')
      | ~ v7_waybel_0(B_467)
      | ~ v4_orders_2(B_467)
      | v2_struct_0(B_467)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1616,c_1318])).

tff(c_1623,plain,(
    ! [B_467] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_467))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_467,'#skF_5')
      | ~ v7_waybel_0(B_467)
      | ~ v4_orders_2(B_467)
      | v2_struct_0(B_467)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1080,c_1082,c_1084,c_1620])).

tff(c_1624,plain,(
    ! [B_467] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_467)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_467))
      | ~ l1_waybel_0(B_467,'#skF_5')
      | ~ v7_waybel_0(B_467)
      | ~ v4_orders_2(B_467)
      | v2_struct_0(B_467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1623])).

tff(c_1642,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1624])).

tff(c_1645,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_1642])).

tff(c_1649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1645])).

tff(c_1651,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1624])).

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

tff(c_1319,plain,(
    ! [A_395,B_396,C_397] :
      ( v4_orders_2('#skF_2'(A_395,B_396,C_397))
      | ~ l1_struct_0(A_395)
      | ~ r3_waybel_9(A_395,B_396,C_397)
      | ~ m1_subset_1(C_397,u1_struct_0(A_395))
      | ~ l1_waybel_0(B_396,A_395)
      | ~ v7_waybel_0(B_396)
      | ~ v4_orders_2(B_396)
      | v2_struct_0(B_396)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_1245,c_28])).

tff(c_1325,plain,(
    ! [A_60,B_396,B_67] :
      ( v4_orders_2('#skF_2'(A_60,B_396,'#skF_3'(A_60,B_67)))
      | ~ l1_struct_0(A_60)
      | ~ r3_waybel_9(A_60,B_396,'#skF_3'(A_60,B_67))
      | ~ l1_waybel_0(B_396,A_60)
      | ~ v7_waybel_0(B_396)
      | ~ v4_orders_2(B_396)
      | v2_struct_0(B_396)
      | ~ l1_waybel_0(B_67,A_60)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_56,c_1319])).

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

tff(c_1294,plain,(
    ! [A_388,B_389,C_390] :
      ( v7_waybel_0('#skF_2'(A_388,B_389,C_390))
      | ~ l1_struct_0(A_388)
      | ~ r3_waybel_9(A_388,B_389,C_390)
      | ~ m1_subset_1(C_390,u1_struct_0(A_388))
      | ~ l1_waybel_0(B_389,A_388)
      | ~ v7_waybel_0(B_389)
      | ~ v4_orders_2(B_389)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(resolution,[status(thm)],[c_1245,c_26])).

tff(c_1300,plain,(
    ! [A_60,B_389,B_67] :
      ( v7_waybel_0('#skF_2'(A_60,B_389,'#skF_3'(A_60,B_67)))
      | ~ l1_struct_0(A_60)
      | ~ r3_waybel_9(A_60,B_389,'#skF_3'(A_60,B_67))
      | ~ l1_waybel_0(B_389,A_60)
      | ~ v7_waybel_0(B_389)
      | ~ v4_orders_2(B_389)
      | v2_struct_0(B_389)
      | ~ l1_waybel_0(B_67,A_60)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_56,c_1294])).

tff(c_1652,plain,(
    ! [B_476] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_476))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_476)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_476)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_476)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_476))
      | ~ l1_waybel_0(B_476,'#skF_5')
      | ~ v7_waybel_0(B_476)
      | ~ v4_orders_2(B_476)
      | v2_struct_0(B_476) ) ),
    inference(splitRight,[status(thm)],[c_1624])).

tff(c_1656,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1300,c_1652])).

tff(c_1659,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1080,c_1082,c_1084,c_1651,c_1656])).

tff(c_1661,plain,(
    ! [B_477] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_477))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_477)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_477)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_477))
      | ~ l1_waybel_0(B_477,'#skF_5')
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1659])).

tff(c_1665,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1325,c_1661])).

tff(c_1668,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1080,c_1082,c_1084,c_1651,c_1665])).

tff(c_1670,plain,(
    ! [B_478] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_478))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_478)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_478))
      | ~ l1_waybel_0(B_478,'#skF_5')
      | ~ v7_waybel_0(B_478)
      | ~ v4_orders_2(B_478)
      | v2_struct_0(B_478) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1668])).

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

tff(c_1264,plain,(
    ! [A_381,B_382,C_383] :
      ( ~ v2_struct_0('#skF_2'(A_381,B_382,C_383))
      | ~ l1_struct_0(A_381)
      | ~ r3_waybel_9(A_381,B_382,C_383)
      | ~ m1_subset_1(C_383,u1_struct_0(A_381))
      | ~ l1_waybel_0(B_382,A_381)
      | ~ v7_waybel_0(B_382)
      | ~ v4_orders_2(B_382)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(resolution,[status(thm)],[c_1245,c_30])).

tff(c_1672,plain,(
    ! [B_478] :
      ( ~ l1_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_5',B_478),u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_478))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_478))
      | ~ l1_waybel_0(B_478,'#skF_5')
      | ~ v7_waybel_0(B_478)
      | ~ v4_orders_2(B_478)
      | v2_struct_0(B_478) ) ),
    inference(resolution,[status(thm)],[c_1670,c_1264])).

tff(c_1675,plain,(
    ! [B_478] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_478),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_478))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_478))
      | ~ l1_waybel_0(B_478,'#skF_5')
      | ~ v7_waybel_0(B_478)
      | ~ v4_orders_2(B_478)
      | v2_struct_0(B_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1080,c_1082,c_1084,c_1651,c_1672])).

tff(c_1677,plain,(
    ! [B_479] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_479),u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_479))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_479))
      | ~ l1_waybel_0(B_479,'#skF_5')
      | ~ v7_waybel_0(B_479)
      | ~ v4_orders_2(B_479)
      | v2_struct_0(B_479) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1675])).

tff(c_1681,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1677])).

tff(c_1684,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1681])).

tff(c_1686,plain,(
    ! [B_480] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_480))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_480))
      | ~ l1_waybel_0(B_480,'#skF_5')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1684])).

tff(c_1270,plain,(
    ! [C_384,A_385,B_386] :
      ( r2_hidden(C_384,k10_yellow_6(A_385,'#skF_2'(A_385,B_386,C_384)))
      | ~ r3_waybel_9(A_385,B_386,C_384)
      | ~ m1_subset_1(C_384,u1_struct_0(A_385))
      | ~ l1_waybel_0(B_386,A_385)
      | ~ v7_waybel_0(B_386)
      | ~ v4_orders_2(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1285,plain,(
    ! [A_385,B_386,C_384] :
      ( ~ r1_tarski(k10_yellow_6(A_385,'#skF_2'(A_385,B_386,C_384)),C_384)
      | ~ r3_waybel_9(A_385,B_386,C_384)
      | ~ m1_subset_1(C_384,u1_struct_0(A_385))
      | ~ l1_waybel_0(B_386,A_385)
      | ~ v7_waybel_0(B_386)
      | ~ v4_orders_2(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_1270,c_18])).

tff(c_1704,plain,(
    ! [B_480] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'('#skF_5',B_480))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_480))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_480),u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_480))
      | ~ l1_waybel_0(B_480,'#skF_5')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_1285])).

tff(c_1736,plain,(
    ! [B_480] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_480),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_480))
      | ~ l1_waybel_0(B_480,'#skF_5')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1080,c_1082,c_1084,c_14,c_1704])).

tff(c_1757,plain,(
    ! [B_481] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_481),u1_struct_0('#skF_5'))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_481))
      | ~ l1_waybel_0(B_481,'#skF_5')
      | ~ v7_waybel_0(B_481)
      | ~ v4_orders_2(B_481)
      | v2_struct_0(B_481) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1736])).

tff(c_1761,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1757])).

tff(c_1764,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_67))
      | ~ l1_waybel_0(B_67,'#skF_5')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1761])).

tff(c_1776,plain,(
    ! [B_486] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_486))
      | ~ l1_waybel_0(B_486,'#skF_5')
      | ~ v7_waybel_0(B_486)
      | ~ v4_orders_2(B_486)
      | v2_struct_0(B_486) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1764])).

tff(c_1784,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1776])).

tff(c_1791,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1077,c_1080,c_1082,c_1084,c_1784])).

tff(c_1793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1076,c_1791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.04  
% 5.32/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.04  %$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 5.32/2.04  
% 5.32/2.04  %Foreground sorts:
% 5.32/2.04  
% 5.32/2.04  
% 5.32/2.04  %Background operators:
% 5.32/2.04  
% 5.32/2.04  
% 5.32/2.04  %Foreground operators:
% 5.32/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.32/2.04  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.32/2.04  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 5.32/2.04  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.32/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/2.04  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.32/2.04  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 5.32/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.32/2.04  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.32/2.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.32/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.32/2.04  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.32/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.32/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.32/2.04  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.32/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.32/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.04  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.32/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.32/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.32/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.32/2.04  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.32/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.04  
% 5.71/2.08  tff(f_250, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 5.71/2.08  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_yellow19)).
% 5.71/2.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.71/2.08  tff(f_73, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 5.71/2.08  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.71/2.08  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 5.71/2.08  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 5.71/2.08  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.71/2.08  tff(f_99, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 5.71/2.08  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.71/2.08  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.71/2.08  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 5.71/2.08  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 5.71/2.08  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.71/2.08  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_72, plain, (~v2_struct_0('#skF_6') | ~v1_compts_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_102, plain, (~v1_compts_1('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 5.71/2.08  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_50, plain, (![A_60]: (v4_orders_2('#skF_4'(A_60)) | v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_98, plain, (![B_79]: (v1_compts_1('#skF_5') | m2_yellow_6('#skF_7'(B_79), '#skF_5', B_79) | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_202, plain, (![B_79]: (m2_yellow_6('#skF_7'(B_79), '#skF_5', B_79) | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_102, c_98])).
% 5.71/2.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.08  tff(c_250, plain, (![A_137, B_138]: (m1_subset_1(k10_yellow_6(A_137, B_138), k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_waybel_0(B_138, A_137) | ~v7_waybel_0(B_138) | ~v4_orders_2(B_138) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.71/2.08  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.71/2.08  tff(c_274, plain, (![A_147, A_148, B_149]: (m1_subset_1(A_147, u1_struct_0(A_148)) | ~r2_hidden(A_147, k10_yellow_6(A_148, B_149)) | ~l1_waybel_0(B_149, A_148) | ~v7_waybel_0(B_149) | ~v4_orders_2(B_149) | v2_struct_0(B_149) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_250, c_16])).
% 5.71/2.08  tff(c_284, plain, (![A_148, B_149, B_2]: (m1_subset_1('#skF_1'(k10_yellow_6(A_148, B_149), B_2), u1_struct_0(A_148)) | ~l1_waybel_0(B_149, A_148) | ~v7_waybel_0(B_149) | ~v4_orders_2(B_149) | v2_struct_0(B_149) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148) | r1_tarski(k10_yellow_6(A_148, B_149), B_2))), inference(resolution, [status(thm)], [c_6, c_274])).
% 5.71/2.08  tff(c_306, plain, (![A_155, B_156, C_157]: (r3_waybel_9(A_155, B_156, C_157) | ~r2_hidden(C_157, k10_yellow_6(A_155, B_156)) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~l1_waybel_0(B_156, A_155) | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.71/2.08  tff(c_398, plain, (![A_198, B_199, B_200]: (r3_waybel_9(A_198, B_199, '#skF_1'(k10_yellow_6(A_198, B_199), B_200)) | ~m1_subset_1('#skF_1'(k10_yellow_6(A_198, B_199), B_200), u1_struct_0(A_198)) | ~l1_waybel_0(B_199, A_198) | ~v7_waybel_0(B_199) | ~v4_orders_2(B_199) | v2_struct_0(B_199) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198) | r1_tarski(k10_yellow_6(A_198, B_199), B_200))), inference(resolution, [status(thm)], [c_6, c_306])).
% 5.71/2.08  tff(c_402, plain, (![A_201, B_202, B_203]: (r3_waybel_9(A_201, B_202, '#skF_1'(k10_yellow_6(A_201, B_202), B_203)) | ~l1_waybel_0(B_202, A_201) | ~v7_waybel_0(B_202) | ~v4_orders_2(B_202) | v2_struct_0(B_202) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201) | r1_tarski(k10_yellow_6(A_201, B_202), B_203))), inference(resolution, [status(thm)], [c_284, c_398])).
% 5.71/2.08  tff(c_38, plain, (![A_31, B_39, D_45, C_43]: (r3_waybel_9(A_31, B_39, D_45) | ~r3_waybel_9(A_31, C_43, D_45) | ~m1_subset_1(D_45, u1_struct_0(A_31)) | ~m2_yellow_6(C_43, A_31, B_39) | ~l1_waybel_0(B_39, A_31) | ~v7_waybel_0(B_39) | ~v4_orders_2(B_39) | v2_struct_0(B_39) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.71/2.08  tff(c_679, plain, (![A_267, B_268, B_269, B_270]: (r3_waybel_9(A_267, B_268, '#skF_1'(k10_yellow_6(A_267, B_269), B_270)) | ~m1_subset_1('#skF_1'(k10_yellow_6(A_267, B_269), B_270), u1_struct_0(A_267)) | ~m2_yellow_6(B_269, A_267, B_268) | ~l1_waybel_0(B_268, A_267) | ~v7_waybel_0(B_268) | ~v4_orders_2(B_268) | v2_struct_0(B_268) | ~l1_waybel_0(B_269, A_267) | ~v7_waybel_0(B_269) | ~v4_orders_2(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267) | r1_tarski(k10_yellow_6(A_267, B_269), B_270))), inference(resolution, [status(thm)], [c_402, c_38])).
% 5.71/2.08  tff(c_689, plain, (![A_275, B_276, B_277, B_278]: (r3_waybel_9(A_275, B_276, '#skF_1'(k10_yellow_6(A_275, B_277), B_278)) | ~m2_yellow_6(B_277, A_275, B_276) | ~l1_waybel_0(B_276, A_275) | ~v7_waybel_0(B_276) | ~v4_orders_2(B_276) | v2_struct_0(B_276) | ~l1_waybel_0(B_277, A_275) | ~v7_waybel_0(B_277) | ~v4_orders_2(B_277) | v2_struct_0(B_277) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275) | r1_tarski(k10_yellow_6(A_275, B_277), B_278))), inference(resolution, [status(thm)], [c_284, c_679])).
% 5.71/2.08  tff(c_44, plain, (![A_60, C_70]: (~r3_waybel_9(A_60, '#skF_4'(A_60), C_70) | ~m1_subset_1(C_70, u1_struct_0(A_60)) | v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_701, plain, (![A_279, B_280, B_281]: (~m1_subset_1('#skF_1'(k10_yellow_6(A_279, B_280), B_281), u1_struct_0(A_279)) | v1_compts_1(A_279) | ~m2_yellow_6(B_280, A_279, '#skF_4'(A_279)) | ~l1_waybel_0('#skF_4'(A_279), A_279) | ~v7_waybel_0('#skF_4'(A_279)) | ~v4_orders_2('#skF_4'(A_279)) | v2_struct_0('#skF_4'(A_279)) | ~l1_waybel_0(B_280, A_279) | ~v7_waybel_0(B_280) | ~v4_orders_2(B_280) | v2_struct_0(B_280) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279) | r1_tarski(k10_yellow_6(A_279, B_280), B_281))), inference(resolution, [status(thm)], [c_689, c_44])).
% 5.71/2.08  tff(c_709, plain, (![A_282, B_283, B_284]: (v1_compts_1(A_282) | ~m2_yellow_6(B_283, A_282, '#skF_4'(A_282)) | ~l1_waybel_0('#skF_4'(A_282), A_282) | ~v7_waybel_0('#skF_4'(A_282)) | ~v4_orders_2('#skF_4'(A_282)) | v2_struct_0('#skF_4'(A_282)) | ~l1_waybel_0(B_283, A_282) | ~v7_waybel_0(B_283) | ~v4_orders_2(B_283) | v2_struct_0(B_283) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282) | r1_tarski(k10_yellow_6(A_282, B_283), B_284))), inference(resolution, [status(thm)], [c_284, c_701])).
% 5.71/2.08  tff(c_715, plain, (![B_284]: (v1_compts_1('#skF_5') | ~l1_waybel_0('#skF_7'('#skF_4'('#skF_5')), '#skF_5') | ~v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) | ~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284) | ~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5')))), inference(resolution, [status(thm)], [c_202, c_709])).
% 5.71/2.08  tff(c_719, plain, (![B_284]: (v1_compts_1('#skF_5') | ~l1_waybel_0('#skF_7'('#skF_4'('#skF_5')), '#skF_5') | ~v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) | ~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_5') | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284) | ~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_715])).
% 5.71/2.08  tff(c_720, plain, (![B_284]: (~l1_waybel_0('#skF_7'('#skF_4'('#skF_5')), '#skF_5') | ~v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) | ~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284) | ~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_719])).
% 5.71/2.08  tff(c_721, plain, (~v4_orders_2('#skF_4'('#skF_5'))), inference(splitLeft, [status(thm)], [c_720])).
% 5.71/2.08  tff(c_724, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_721])).
% 5.71/2.08  tff(c_727, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_724])).
% 5.71/2.08  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_727])).
% 5.71/2.08  tff(c_731, plain, (v4_orders_2('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_720])).
% 5.71/2.08  tff(c_48, plain, (![A_60]: (v7_waybel_0('#skF_4'(A_60)) | v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_46, plain, (![A_60]: (l1_waybel_0('#skF_4'(A_60), A_60) | v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.71/2.08  tff(c_205, plain, (![C_121, A_122, B_123]: (v4_orders_2(C_121) | ~m2_yellow_6(C_121, A_122, B_123) | ~l1_waybel_0(B_123, A_122) | ~v7_waybel_0(B_123) | ~v4_orders_2(B_123) | v2_struct_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_208, plain, (![B_79]: (v4_orders_2('#skF_7'(B_79)) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(resolution, [status(thm)], [c_202, c_205])).
% 5.71/2.08  tff(c_211, plain, (![B_79]: (v4_orders_2('#skF_7'(B_79)) | ~l1_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_62, c_208])).
% 5.71/2.08  tff(c_212, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_211])).
% 5.71/2.08  tff(c_215, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_212])).
% 5.71/2.08  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_215])).
% 5.71/2.08  tff(c_221, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_211])).
% 5.71/2.08  tff(c_241, plain, (![C_133, A_134, B_135]: (l1_waybel_0(C_133, A_134) | ~m2_yellow_6(C_133, A_134, B_135) | ~l1_waybel_0(B_135, A_134) | ~v7_waybel_0(B_135) | ~v4_orders_2(B_135) | v2_struct_0(B_135) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_244, plain, (![B_79]: (l1_waybel_0('#skF_7'(B_79), '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(resolution, [status(thm)], [c_202, c_241])).
% 5.71/2.08  tff(c_247, plain, (![B_79]: (l1_waybel_0('#skF_7'(B_79), '#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_244])).
% 5.71/2.08  tff(c_248, plain, (![B_79]: (l1_waybel_0('#skF_7'(B_79), '#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_62, c_247])).
% 5.71/2.08  tff(c_730, plain, (![B_284]: (~v7_waybel_0('#skF_4'('#skF_5')) | ~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | ~v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) | ~l1_waybel_0('#skF_7'('#skF_4'('#skF_5')), '#skF_5') | v2_struct_0('#skF_4'('#skF_5')) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_720])).
% 5.71/2.08  tff(c_742, plain, (~l1_waybel_0('#skF_7'('#skF_4'('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_730])).
% 5.71/2.08  tff(c_745, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_248, c_742])).
% 5.71/2.08  tff(c_748, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_745])).
% 5.71/2.08  tff(c_749, plain, (~v7_waybel_0('#skF_4'('#skF_5'))), inference(splitLeft, [status(thm)], [c_748])).
% 5.71/2.08  tff(c_752, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_749])).
% 5.71/2.08  tff(c_755, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_752])).
% 5.71/2.08  tff(c_757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_755])).
% 5.71/2.08  tff(c_758, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | v2_struct_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_748])).
% 5.71/2.08  tff(c_760, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_758])).
% 5.71/2.08  tff(c_763, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_760])).
% 5.71/2.08  tff(c_766, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_763])).
% 5.71/2.08  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_766])).
% 5.71/2.08  tff(c_769, plain, (v2_struct_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_758])).
% 5.71/2.08  tff(c_52, plain, (![A_60]: (~v2_struct_0('#skF_4'(A_60)) | v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_773, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_769, c_52])).
% 5.71/2.08  tff(c_776, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_773])).
% 5.71/2.08  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_776])).
% 5.71/2.08  tff(c_779, plain, (![B_284]: (~v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) | ~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | ~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_4'('#skF_5')) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_730])).
% 5.71/2.08  tff(c_787, plain, (~v7_waybel_0('#skF_4'('#skF_5'))), inference(splitLeft, [status(thm)], [c_779])).
% 5.71/2.08  tff(c_790, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_787])).
% 5.71/2.08  tff(c_793, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_790])).
% 5.71/2.08  tff(c_795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_793])).
% 5.71/2.08  tff(c_797, plain, (v7_waybel_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_779])).
% 5.71/2.08  tff(c_223, plain, (![C_125, A_126, B_127]: (v7_waybel_0(C_125) | ~m2_yellow_6(C_125, A_126, B_127) | ~l1_waybel_0(B_127, A_126) | ~v7_waybel_0(B_127) | ~v4_orders_2(B_127) | v2_struct_0(B_127) | ~l1_struct_0(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_226, plain, (![B_79]: (v7_waybel_0('#skF_7'(B_79)) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(resolution, [status(thm)], [c_202, c_223])).
% 5.71/2.08  tff(c_229, plain, (![B_79]: (v7_waybel_0('#skF_7'(B_79)) | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_226])).
% 5.71/2.08  tff(c_230, plain, (![B_79]: (v7_waybel_0('#skF_7'(B_79)) | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_62, c_229])).
% 5.71/2.08  tff(c_796, plain, (![B_284]: (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | ~v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_4'('#skF_5')) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_779])).
% 5.71/2.08  tff(c_798, plain, (~v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))), inference(splitLeft, [status(thm)], [c_796])).
% 5.71/2.08  tff(c_801, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_230, c_798])).
% 5.71/2.08  tff(c_804, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | v2_struct_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_797, c_801])).
% 5.71/2.08  tff(c_805, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_804])).
% 5.71/2.08  tff(c_808, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_805])).
% 5.71/2.08  tff(c_811, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_808])).
% 5.71/2.08  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_811])).
% 5.71/2.08  tff(c_814, plain, (v2_struct_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_804])).
% 5.71/2.08  tff(c_818, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_814, c_52])).
% 5.71/2.08  tff(c_821, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_818])).
% 5.71/2.08  tff(c_823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_821])).
% 5.71/2.08  tff(c_824, plain, (![B_284]: (~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | ~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_4'('#skF_5')) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_796])).
% 5.71/2.08  tff(c_836, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_824])).
% 5.71/2.08  tff(c_839, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_836])).
% 5.71/2.08  tff(c_842, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_839])).
% 5.71/2.08  tff(c_844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_842])).
% 5.71/2.08  tff(c_846, plain, (l1_waybel_0('#skF_4'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_824])).
% 5.71/2.08  tff(c_220, plain, (![B_79]: (v4_orders_2('#skF_7'(B_79)) | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(splitRight, [status(thm)], [c_211])).
% 5.71/2.08  tff(c_845, plain, (![B_284]: (~v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_4'('#skF_5')) | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_824])).
% 5.71/2.08  tff(c_865, plain, (~v4_orders_2('#skF_7'('#skF_4'('#skF_5')))), inference(splitLeft, [status(thm)], [c_845])).
% 5.71/2.08  tff(c_868, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_220, c_865])).
% 5.71/2.08  tff(c_871, plain, (v2_struct_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_797, c_846, c_868])).
% 5.71/2.08  tff(c_874, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_871, c_52])).
% 5.71/2.08  tff(c_877, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_874])).
% 5.71/2.08  tff(c_879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_877])).
% 5.71/2.08  tff(c_880, plain, (![B_284]: (v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | v2_struct_0('#skF_4'('#skF_5')) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_845])).
% 5.71/2.08  tff(c_894, plain, (v2_struct_0('#skF_4'('#skF_5'))), inference(splitLeft, [status(thm)], [c_880])).
% 5.71/2.08  tff(c_897, plain, (v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_894, c_52])).
% 5.71/2.08  tff(c_900, plain, (v1_compts_1('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_897])).
% 5.71/2.08  tff(c_902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_102, c_900])).
% 5.71/2.08  tff(c_904, plain, (~v2_struct_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_880])).
% 5.71/2.08  tff(c_903, plain, (![B_284]: (v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) | r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_284))), inference(splitRight, [status(thm)], [c_880])).
% 5.71/2.08  tff(c_929, plain, (v2_struct_0('#skF_7'('#skF_4'('#skF_5')))), inference(splitLeft, [status(thm)], [c_903])).
% 5.71/2.08  tff(c_232, plain, (![C_129, A_130, B_131]: (~v2_struct_0(C_129) | ~m2_yellow_6(C_129, A_130, B_131) | ~l1_waybel_0(B_131, A_130) | ~v7_waybel_0(B_131) | ~v4_orders_2(B_131) | v2_struct_0(B_131) | ~l1_struct_0(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_235, plain, (![B_79]: (~v2_struct_0('#skF_7'(B_79)) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(resolution, [status(thm)], [c_202, c_232])).
% 5.71/2.08  tff(c_238, plain, (![B_79]: (~v2_struct_0('#skF_7'(B_79)) | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_235])).
% 5.71/2.08  tff(c_239, plain, (![B_79]: (~v2_struct_0('#skF_7'(B_79)) | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_62, c_238])).
% 5.71/2.08  tff(c_932, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_929, c_239])).
% 5.71/2.08  tff(c_935, plain, (v2_struct_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_797, c_846, c_932])).
% 5.71/2.08  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_904, c_935])).
% 5.71/2.08  tff(c_940, plain, (![B_308]: (r1_tarski(k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5'))), B_308))), inference(splitRight, [status(thm)], [c_903])).
% 5.71/2.08  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.71/2.08  tff(c_117, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.71/2.08  tff(c_126, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_117])).
% 5.71/2.08  tff(c_992, plain, (k10_yellow_6('#skF_5', '#skF_7'('#skF_4'('#skF_5')))=k1_xboole_0), inference(resolution, [status(thm)], [c_940, c_126])).
% 5.71/2.08  tff(c_86, plain, (![B_79]: (v1_compts_1('#skF_5') | v3_yellow_6('#skF_7'(B_79), '#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_192, plain, (![B_79]: (v3_yellow_6('#skF_7'(B_79), '#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_102, c_86])).
% 5.71/2.08  tff(c_254, plain, (![A_139, B_140]: (k10_yellow_6(A_139, B_140)!=k1_xboole_0 | ~v3_yellow_6(B_140, A_139) | ~l1_waybel_0(B_140, A_139) | ~v7_waybel_0(B_140) | ~v4_orders_2(B_140) | v2_struct_0(B_140) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.08  tff(c_257, plain, (![B_79]: (k10_yellow_6('#skF_5', '#skF_7'(B_79))!=k1_xboole_0 | ~l1_waybel_0('#skF_7'(B_79), '#skF_5') | ~v7_waybel_0('#skF_7'(B_79)) | ~v4_orders_2('#skF_7'(B_79)) | v2_struct_0('#skF_7'(B_79)) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(resolution, [status(thm)], [c_192, c_254])).
% 5.71/2.08  tff(c_260, plain, (![B_79]: (k10_yellow_6('#skF_5', '#skF_7'(B_79))!=k1_xboole_0 | ~l1_waybel_0('#skF_7'(B_79), '#skF_5') | ~v7_waybel_0('#skF_7'(B_79)) | ~v4_orders_2('#skF_7'(B_79)) | v2_struct_0('#skF_7'(B_79)) | v2_struct_0('#skF_5') | ~l1_waybel_0(B_79, '#skF_5') | ~v7_waybel_0(B_79) | ~v4_orders_2(B_79) | v2_struct_0(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_257])).
% 5.71/2.08  tff(c_285, plain, (![B_150]: (k10_yellow_6('#skF_5', '#skF_7'(B_150))!=k1_xboole_0 | ~l1_waybel_0('#skF_7'(B_150), '#skF_5') | ~v7_waybel_0('#skF_7'(B_150)) | ~v4_orders_2('#skF_7'(B_150)) | v2_struct_0('#skF_7'(B_150)) | ~l1_waybel_0(B_150, '#skF_5') | ~v7_waybel_0(B_150) | ~v4_orders_2(B_150) | v2_struct_0(B_150))), inference(negUnitSimplification, [status(thm)], [c_62, c_260])).
% 5.71/2.08  tff(c_290, plain, (![B_151]: (k10_yellow_6('#skF_5', '#skF_7'(B_151))!=k1_xboole_0 | ~v7_waybel_0('#skF_7'(B_151)) | ~v4_orders_2('#skF_7'(B_151)) | v2_struct_0('#skF_7'(B_151)) | ~l1_waybel_0(B_151, '#skF_5') | ~v7_waybel_0(B_151) | ~v4_orders_2(B_151) | v2_struct_0(B_151))), inference(resolution, [status(thm)], [c_248, c_285])).
% 5.71/2.08  tff(c_295, plain, (![B_152]: (k10_yellow_6('#skF_5', '#skF_7'(B_152))!=k1_xboole_0 | ~v4_orders_2('#skF_7'(B_152)) | v2_struct_0('#skF_7'(B_152)) | ~l1_waybel_0(B_152, '#skF_5') | ~v7_waybel_0(B_152) | ~v4_orders_2(B_152) | v2_struct_0(B_152))), inference(resolution, [status(thm)], [c_230, c_290])).
% 5.71/2.08  tff(c_300, plain, (![B_153]: (k10_yellow_6('#skF_5', '#skF_7'(B_153))!=k1_xboole_0 | v2_struct_0('#skF_7'(B_153)) | ~l1_waybel_0(B_153, '#skF_5') | ~v7_waybel_0(B_153) | ~v4_orders_2(B_153) | v2_struct_0(B_153))), inference(resolution, [status(thm)], [c_220, c_295])).
% 5.71/2.08  tff(c_304, plain, (![B_153]: (k10_yellow_6('#skF_5', '#skF_7'(B_153))!=k1_xboole_0 | ~l1_waybel_0(B_153, '#skF_5') | ~v7_waybel_0(B_153) | ~v4_orders_2(B_153) | v2_struct_0(B_153))), inference(resolution, [status(thm)], [c_300, c_239])).
% 5.71/2.08  tff(c_1029, plain, (~l1_waybel_0('#skF_4'('#skF_5'), '#skF_5') | ~v7_waybel_0('#skF_4'('#skF_5')) | ~v4_orders_2('#skF_4'('#skF_5')) | v2_struct_0('#skF_4'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_992, c_304])).
% 5.71/2.08  tff(c_1073, plain, (v2_struct_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_797, c_846, c_1029])).
% 5.71/2.08  tff(c_1075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_904, c_1073])).
% 5.71/2.08  tff(c_1076, plain, (~v2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 5.71/2.08  tff(c_1077, plain, (v1_compts_1('#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 5.71/2.08  tff(c_70, plain, (v4_orders_2('#skF_6') | ~v1_compts_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_1080, plain, (v4_orders_2('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_70])).
% 5.71/2.08  tff(c_68, plain, (v7_waybel_0('#skF_6') | ~v1_compts_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_1082, plain, (v7_waybel_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_68])).
% 5.71/2.08  tff(c_66, plain, (l1_waybel_0('#skF_6', '#skF_5') | ~v1_compts_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_1084, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_66])).
% 5.71/2.08  tff(c_54, plain, (![A_60, B_67]: (r3_waybel_9(A_60, B_67, '#skF_3'(A_60, B_67)) | ~l1_waybel_0(B_67, A_60) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_56, plain, (![A_60, B_67]: (m1_subset_1('#skF_3'(A_60, B_67), u1_struct_0(A_60)) | ~l1_waybel_0(B_67, A_60) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.71/2.08  tff(c_1245, plain, (![A_381, B_382, C_383]: (m2_yellow_6('#skF_2'(A_381, B_382, C_383), A_381, B_382) | ~r3_waybel_9(A_381, B_382, C_383) | ~m1_subset_1(C_383, u1_struct_0(A_381)) | ~l1_waybel_0(B_382, A_381) | ~v7_waybel_0(B_382) | ~v4_orders_2(B_382) | v2_struct_0(B_382) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.71/2.08  tff(c_24, plain, (![C_20, A_17, B_18]: (l1_waybel_0(C_20, A_17) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_1331, plain, (![A_405, B_406, C_407]: (l1_waybel_0('#skF_2'(A_405, B_406, C_407), A_405) | ~l1_struct_0(A_405) | ~r3_waybel_9(A_405, B_406, C_407) | ~m1_subset_1(C_407, u1_struct_0(A_405)) | ~l1_waybel_0(B_406, A_405) | ~v7_waybel_0(B_406) | ~v4_orders_2(B_406) | v2_struct_0(B_406) | ~l1_pre_topc(A_405) | ~v2_pre_topc(A_405) | v2_struct_0(A_405))), inference(resolution, [status(thm)], [c_1245, c_24])).
% 5.71/2.08  tff(c_1616, plain, (![A_465, B_466, B_467]: (l1_waybel_0('#skF_2'(A_465, B_466, '#skF_3'(A_465, B_467)), A_465) | ~l1_struct_0(A_465) | ~r3_waybel_9(A_465, B_466, '#skF_3'(A_465, B_467)) | ~l1_waybel_0(B_466, A_465) | ~v7_waybel_0(B_466) | ~v4_orders_2(B_466) | v2_struct_0(B_466) | ~l1_waybel_0(B_467, A_465) | ~v7_waybel_0(B_467) | ~v4_orders_2(B_467) | v2_struct_0(B_467) | ~v1_compts_1(A_465) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(resolution, [status(thm)], [c_56, c_1331])).
% 5.71/2.08  tff(c_32, plain, (![B_23, A_21]: (v3_yellow_6(B_23, A_21) | k10_yellow_6(A_21, B_23)=k1_xboole_0 | ~l1_waybel_0(B_23, A_21) | ~v7_waybel_0(B_23) | ~v4_orders_2(B_23) | v2_struct_0(B_23) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.08  tff(c_64, plain, (![C_78]: (~v3_yellow_6(C_78, '#skF_5') | ~m2_yellow_6(C_78, '#skF_5', '#skF_6') | ~v1_compts_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 5.71/2.08  tff(c_1109, plain, (![C_78]: (~v3_yellow_6(C_78, '#skF_5') | ~m2_yellow_6(C_78, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_64])).
% 5.71/2.08  tff(c_1261, plain, (![C_383]: (~v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_383), '#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', C_383) | ~m1_subset_1(C_383, u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1245, c_1109])).
% 5.71/2.08  tff(c_1268, plain, (![C_383]: (~v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_383), '#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', C_383) | ~m1_subset_1(C_383, u1_struct_0('#skF_5')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1080, c_1082, c_1084, c_1261])).
% 5.71/2.08  tff(c_1286, plain, (![C_387]: (~v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_387), '#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', C_387) | ~m1_subset_1(C_387, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1268])).
% 5.71/2.08  tff(c_1289, plain, (![C_387]: (~r3_waybel_9('#skF_5', '#skF_6', C_387) | ~m1_subset_1(C_387, u1_struct_0('#skF_5')) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_387))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', C_387), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', C_387)) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', C_387)) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', C_387)) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_1286])).
% 5.71/2.08  tff(c_1292, plain, (![C_387]: (~r3_waybel_9('#skF_5', '#skF_6', C_387) | ~m1_subset_1(C_387, u1_struct_0('#skF_5')) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_387))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', C_387), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', C_387)) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', C_387)) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', C_387)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1289])).
% 5.71/2.08  tff(c_1302, plain, (![C_394]: (~r3_waybel_9('#skF_5', '#skF_6', C_394) | ~m1_subset_1(C_394, u1_struct_0('#skF_5')) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_394))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', C_394), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', C_394)) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', C_394)) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', C_394)))), inference(negUnitSimplification, [status(thm)], [c_62, c_1292])).
% 5.71/2.08  tff(c_1310, plain, (![B_67]: (~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1302])).
% 5.71/2.08  tff(c_1317, plain, (![B_67]: (~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1310])).
% 5.71/2.08  tff(c_1318, plain, (![B_67]: (~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67))), inference(negUnitSimplification, [status(thm)], [c_62, c_1317])).
% 5.71/2.08  tff(c_1620, plain, (![B_467]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | ~l1_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467)) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_467, '#skF_5') | ~v7_waybel_0(B_467) | ~v4_orders_2(B_467) | v2_struct_0(B_467) | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1616, c_1318])).
% 5.71/2.08  tff(c_1623, plain, (![B_467]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | ~l1_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_467, '#skF_5') | ~v7_waybel_0(B_467) | ~v4_orders_2(B_467) | v2_struct_0(B_467) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1080, c_1082, c_1084, c_1620])).
% 5.71/2.08  tff(c_1624, plain, (![B_467]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467))) | ~l1_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_467)) | ~l1_waybel_0(B_467, '#skF_5') | ~v7_waybel_0(B_467) | ~v4_orders_2(B_467) | v2_struct_0(B_467))), inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1623])).
% 5.71/2.08  tff(c_1642, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1624])).
% 5.71/2.08  tff(c_1645, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_1642])).
% 5.71/2.08  tff(c_1649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1645])).
% 5.71/2.08  tff(c_1651, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1624])).
% 5.71/2.08  tff(c_28, plain, (![C_20, A_17, B_18]: (v4_orders_2(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_1319, plain, (![A_395, B_396, C_397]: (v4_orders_2('#skF_2'(A_395, B_396, C_397)) | ~l1_struct_0(A_395) | ~r3_waybel_9(A_395, B_396, C_397) | ~m1_subset_1(C_397, u1_struct_0(A_395)) | ~l1_waybel_0(B_396, A_395) | ~v7_waybel_0(B_396) | ~v4_orders_2(B_396) | v2_struct_0(B_396) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(resolution, [status(thm)], [c_1245, c_28])).
% 5.71/2.08  tff(c_1325, plain, (![A_60, B_396, B_67]: (v4_orders_2('#skF_2'(A_60, B_396, '#skF_3'(A_60, B_67))) | ~l1_struct_0(A_60) | ~r3_waybel_9(A_60, B_396, '#skF_3'(A_60, B_67)) | ~l1_waybel_0(B_396, A_60) | ~v7_waybel_0(B_396) | ~v4_orders_2(B_396) | v2_struct_0(B_396) | ~l1_waybel_0(B_67, A_60) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_56, c_1319])).
% 5.71/2.08  tff(c_26, plain, (![C_20, A_17, B_18]: (v7_waybel_0(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_1294, plain, (![A_388, B_389, C_390]: (v7_waybel_0('#skF_2'(A_388, B_389, C_390)) | ~l1_struct_0(A_388) | ~r3_waybel_9(A_388, B_389, C_390) | ~m1_subset_1(C_390, u1_struct_0(A_388)) | ~l1_waybel_0(B_389, A_388) | ~v7_waybel_0(B_389) | ~v4_orders_2(B_389) | v2_struct_0(B_389) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(resolution, [status(thm)], [c_1245, c_26])).
% 5.71/2.08  tff(c_1300, plain, (![A_60, B_389, B_67]: (v7_waybel_0('#skF_2'(A_60, B_389, '#skF_3'(A_60, B_67))) | ~l1_struct_0(A_60) | ~r3_waybel_9(A_60, B_389, '#skF_3'(A_60, B_67)) | ~l1_waybel_0(B_389, A_60) | ~v7_waybel_0(B_389) | ~v4_orders_2(B_389) | v2_struct_0(B_389) | ~l1_waybel_0(B_67, A_60) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_56, c_1294])).
% 5.71/2.08  tff(c_1652, plain, (![B_476]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_476)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_476))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_476))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_476))) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_476)) | ~l1_waybel_0(B_476, '#skF_5') | ~v7_waybel_0(B_476) | ~v4_orders_2(B_476) | v2_struct_0(B_476))), inference(splitRight, [status(thm)], [c_1624])).
% 5.71/2.08  tff(c_1656, plain, (![B_67]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~l1_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1300, c_1652])).
% 5.71/2.08  tff(c_1659, plain, (![B_67]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1080, c_1082, c_1084, c_1651, c_1656])).
% 5.71/2.08  tff(c_1661, plain, (![B_477]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_477)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_477))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_477))) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_477)) | ~l1_waybel_0(B_477, '#skF_5') | ~v7_waybel_0(B_477) | ~v4_orders_2(B_477) | v2_struct_0(B_477))), inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1659])).
% 5.71/2.08  tff(c_1665, plain, (![B_67]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~l1_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1325, c_1661])).
% 5.71/2.08  tff(c_1668, plain, (![B_67]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67))) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1080, c_1082, c_1084, c_1651, c_1665])).
% 5.71/2.08  tff(c_1670, plain, (![B_478]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478))) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478)) | ~l1_waybel_0(B_478, '#skF_5') | ~v7_waybel_0(B_478) | ~v4_orders_2(B_478) | v2_struct_0(B_478))), inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1668])).
% 5.71/2.08  tff(c_30, plain, (![C_20, A_17, B_18]: (~v2_struct_0(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.71/2.08  tff(c_1264, plain, (![A_381, B_382, C_383]: (~v2_struct_0('#skF_2'(A_381, B_382, C_383)) | ~l1_struct_0(A_381) | ~r3_waybel_9(A_381, B_382, C_383) | ~m1_subset_1(C_383, u1_struct_0(A_381)) | ~l1_waybel_0(B_382, A_381) | ~v7_waybel_0(B_382) | ~v4_orders_2(B_382) | v2_struct_0(B_382) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(resolution, [status(thm)], [c_1245, c_30])).
% 5.71/2.08  tff(c_1672, plain, (![B_478]: (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', B_478), u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478)))=k1_xboole_0 | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478)) | ~l1_waybel_0(B_478, '#skF_5') | ~v7_waybel_0(B_478) | ~v4_orders_2(B_478) | v2_struct_0(B_478))), inference(resolution, [status(thm)], [c_1670, c_1264])).
% 5.71/2.08  tff(c_1675, plain, (![B_478]: (~m1_subset_1('#skF_3'('#skF_5', B_478), u1_struct_0('#skF_5')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478)))=k1_xboole_0 | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_478)) | ~l1_waybel_0(B_478, '#skF_5') | ~v7_waybel_0(B_478) | ~v4_orders_2(B_478) | v2_struct_0(B_478))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1080, c_1082, c_1084, c_1651, c_1672])).
% 5.71/2.08  tff(c_1677, plain, (![B_479]: (~m1_subset_1('#skF_3'('#skF_5', B_479), u1_struct_0('#skF_5')) | k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_479)))=k1_xboole_0 | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_479)) | ~l1_waybel_0(B_479, '#skF_5') | ~v7_waybel_0(B_479) | ~v4_orders_2(B_479) | v2_struct_0(B_479))), inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1675])).
% 5.71/2.08  tff(c_1681, plain, (![B_67]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1677])).
% 5.71/2.08  tff(c_1684, plain, (![B_67]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)))=k1_xboole_0 | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1681])).
% 5.71/2.08  tff(c_1686, plain, (![B_480]: (k10_yellow_6('#skF_5', '#skF_2'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_480)))=k1_xboole_0 | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_480)) | ~l1_waybel_0(B_480, '#skF_5') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480))), inference(negUnitSimplification, [status(thm)], [c_62, c_1684])).
% 5.71/2.08  tff(c_1270, plain, (![C_384, A_385, B_386]: (r2_hidden(C_384, k10_yellow_6(A_385, '#skF_2'(A_385, B_386, C_384))) | ~r3_waybel_9(A_385, B_386, C_384) | ~m1_subset_1(C_384, u1_struct_0(A_385)) | ~l1_waybel_0(B_386, A_385) | ~v7_waybel_0(B_386) | ~v4_orders_2(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.71/2.08  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.71/2.08  tff(c_1285, plain, (![A_385, B_386, C_384]: (~r1_tarski(k10_yellow_6(A_385, '#skF_2'(A_385, B_386, C_384)), C_384) | ~r3_waybel_9(A_385, B_386, C_384) | ~m1_subset_1(C_384, u1_struct_0(A_385)) | ~l1_waybel_0(B_386, A_385) | ~v7_waybel_0(B_386) | ~v4_orders_2(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(resolution, [status(thm)], [c_1270, c_18])).
% 5.71/2.08  tff(c_1704, plain, (![B_480]: (~r1_tarski(k1_xboole_0, '#skF_3'('#skF_5', B_480)) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_480)) | ~m1_subset_1('#skF_3'('#skF_5', B_480), u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_480)) | ~l1_waybel_0(B_480, '#skF_5') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480))), inference(superposition, [status(thm), theory('equality')], [c_1686, c_1285])).
% 5.71/2.08  tff(c_1736, plain, (![B_480]: (~m1_subset_1('#skF_3'('#skF_5', B_480), u1_struct_0('#skF_5')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_480)) | ~l1_waybel_0(B_480, '#skF_5') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1080, c_1082, c_1084, c_14, c_1704])).
% 5.71/2.08  tff(c_1757, plain, (![B_481]: (~m1_subset_1('#skF_3'('#skF_5', B_481), u1_struct_0('#skF_5')) | ~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_481)) | ~l1_waybel_0(B_481, '#skF_5') | ~v7_waybel_0(B_481) | ~v4_orders_2(B_481) | v2_struct_0(B_481))), inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1736])).
% 5.71/2.08  tff(c_1761, plain, (![B_67]: (~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1757])).
% 5.71/2.08  tff(c_1764, plain, (![B_67]: (~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_67)) | ~l1_waybel_0(B_67, '#skF_5') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1761])).
% 5.71/2.08  tff(c_1776, plain, (![B_486]: (~r3_waybel_9('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_486)) | ~l1_waybel_0(B_486, '#skF_5') | ~v7_waybel_0(B_486) | ~v4_orders_2(B_486) | v2_struct_0(B_486))), inference(negUnitSimplification, [status(thm)], [c_62, c_1764])).
% 5.71/2.08  tff(c_1784, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~v1_compts_1('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1776])).
% 5.71/2.08  tff(c_1791, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1077, c_1080, c_1082, c_1084, c_1784])).
% 5.71/2.08  tff(c_1793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1076, c_1791])).
% 5.71/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.08  
% 5.71/2.08  Inference rules
% 5.71/2.08  ----------------------
% 5.71/2.08  #Ref     : 0
% 5.71/2.08  #Sup     : 326
% 5.71/2.08  #Fact    : 0
% 5.71/2.08  #Define  : 0
% 5.71/2.08  #Split   : 17
% 5.71/2.08  #Chain   : 0
% 5.71/2.08  #Close   : 0
% 5.71/2.08  
% 5.71/2.08  Ordering : KBO
% 5.71/2.08  
% 5.71/2.08  Simplification rules
% 5.71/2.08  ----------------------
% 5.71/2.08  #Subsume      : 138
% 5.71/2.08  #Demod        : 289
% 5.71/2.08  #Tautology    : 80
% 5.71/2.08  #SimpNegUnit  : 66
% 5.71/2.08  #BackRed      : 1
% 5.71/2.08  
% 5.71/2.08  #Partial instantiations: 0
% 5.71/2.08  #Strategies tried      : 1
% 5.71/2.08  
% 5.71/2.08  Timing (in seconds)
% 5.71/2.08  ----------------------
% 5.71/2.09  Preprocessing        : 0.37
% 5.71/2.09  Parsing              : 0.21
% 5.71/2.09  CNF conversion       : 0.03
% 5.71/2.09  Main loop            : 0.86
% 5.71/2.09  Inferencing          : 0.33
% 5.83/2.09  Reduction            : 0.24
% 5.83/2.09  Demodulation         : 0.16
% 5.83/2.09  BG Simplification    : 0.04
% 5.83/2.09  Subsumption          : 0.21
% 5.83/2.09  Abstraction          : 0.03
% 5.83/2.09  MUC search           : 0.00
% 5.83/2.09  Cooper               : 0.00
% 5.83/2.09  Total                : 1.31
% 5.83/2.09  Index Insertion      : 0.00
% 5.83/2.09  Index Deletion       : 0.00
% 5.83/2.09  Index Matching       : 0.00
% 5.83/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
