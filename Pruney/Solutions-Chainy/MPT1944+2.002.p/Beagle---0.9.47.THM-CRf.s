%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:54 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 170 expanded)
%              Number of leaves         :   39 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          :  311 ( 966 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > m1_connsp_2 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_5 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k4_yellow_6,type,(
    k4_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A] :
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

tff(f_137,axiom,(
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

tff(f_119,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_168,axiom,(
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

tff(c_58,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_48,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_42,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1(k4_yellow_6(A_154,B_155),u1_struct_0(A_154))
      | ~ l1_waybel_0(B_155,A_154)
      | ~ l1_struct_0(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_60,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_54,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_52,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_50,plain,(
    v1_yellow_6('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_40,plain,(
    ! [A_152,B_153] :
      ( m1_subset_1(k10_yellow_6(A_152,B_153),k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_waybel_0(B_153,A_152)
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_141,plain,(
    ! [A_227,B_228,D_229] :
      ( m1_connsp_2('#skF_4'(A_227,B_228,k10_yellow_6(A_227,B_228),D_229),A_227,D_229)
      | r2_hidden(D_229,k10_yellow_6(A_227,B_228))
      | ~ m1_subset_1(D_229,u1_struct_0(A_227))
      | ~ m1_subset_1(k10_yellow_6(A_227,B_228),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_waybel_0(B_228,A_227)
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_145,plain,(
    ! [A_230,B_231,D_232] :
      ( m1_connsp_2('#skF_4'(A_230,B_231,k10_yellow_6(A_230,B_231),D_232),A_230,D_232)
      | r2_hidden(D_232,k10_yellow_6(A_230,B_231))
      | ~ m1_subset_1(D_232,u1_struct_0(A_230))
      | ~ l1_waybel_0(B_231,A_230)
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_6,plain,(
    ! [C_7,A_4,B_5] :
      ( m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_connsp_2(C_7,A_4,B_5)
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_158,plain,(
    ! [A_230,B_231,D_232] :
      ( m1_subset_1('#skF_4'(A_230,B_231,k10_yellow_6(A_230,B_231),D_232),k1_zfmisc_1(u1_struct_0(A_230)))
      | r2_hidden(D_232,k10_yellow_6(A_230,B_231))
      | ~ m1_subset_1(D_232,u1_struct_0(A_230))
      | ~ l1_waybel_0(B_231,A_230)
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_8,plain,(
    ! [C_14,B_12,A_8] :
      ( r2_hidden(C_14,B_12)
      | ~ m1_connsp_2(B_12,A_8,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_8))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_202,plain,(
    ! [D_256,A_257,B_258] :
      ( r2_hidden(D_256,'#skF_4'(A_257,B_258,k10_yellow_6(A_257,B_258),D_256))
      | ~ m1_subset_1('#skF_4'(A_257,B_258,k10_yellow_6(A_257,B_258),D_256),k1_zfmisc_1(u1_struct_0(A_257)))
      | r2_hidden(D_256,k10_yellow_6(A_257,B_258))
      | ~ m1_subset_1(D_256,u1_struct_0(A_257))
      | ~ l1_waybel_0(B_258,A_257)
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_207,plain,(
    ! [D_262,A_263,B_264] :
      ( r2_hidden(D_262,'#skF_4'(A_263,B_264,k10_yellow_6(A_263,B_264),D_262))
      | r2_hidden(D_262,k10_yellow_6(A_263,B_264))
      | ~ m1_subset_1(D_262,u1_struct_0(A_263))
      | ~ l1_waybel_0(B_264,A_263)
      | ~ v7_waybel_0(B_264)
      | ~ v4_orders_2(B_264)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(resolution,[status(thm)],[c_158,c_202])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18,plain,(
    ! [A_15,B_43,C_57,D_64] :
      ( m1_subset_1('#skF_2'(A_15,B_43,C_57,D_64),u1_struct_0(B_43))
      | r1_waybel_0(A_15,B_43,C_57)
      | ~ m1_subset_1(D_64,u1_struct_0(B_43))
      | ~ l1_waybel_0(B_43,A_15)
      | v2_struct_0(B_43)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_72,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_waybel_0(A_187,B_188,C_189) = k4_yellow_6(A_187,B_188)
      | ~ m1_subset_1(C_189,u1_struct_0(B_188))
      | ~ l1_waybel_0(B_188,A_187)
      | ~ v1_yellow_6(B_188,A_187)
      | ~ v7_waybel_0(B_188)
      | ~ v4_orders_2(B_188)
      | v2_struct_0(B_188)
      | ~ l1_struct_0(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_161,plain,(
    ! [C_244,D_242,A_241,B_240,A_243] :
      ( k2_waybel_0(A_241,B_240,'#skF_2'(A_243,B_240,C_244,D_242)) = k4_yellow_6(A_241,B_240)
      | ~ l1_waybel_0(B_240,A_241)
      | ~ v1_yellow_6(B_240,A_241)
      | ~ v7_waybel_0(B_240)
      | ~ v4_orders_2(B_240)
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241)
      | r1_waybel_0(A_243,B_240,C_244)
      | ~ m1_subset_1(D_242,u1_struct_0(B_240))
      | ~ l1_waybel_0(B_240,A_243)
      | v2_struct_0(B_240)
      | ~ l1_struct_0(A_243)
      | v2_struct_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_186,plain,(
    ! [A_249,B_250,A_251,C_252] :
      ( k2_waybel_0(A_249,B_250,'#skF_2'(A_251,B_250,C_252,'#skF_1'(u1_struct_0(B_250)))) = k4_yellow_6(A_249,B_250)
      | ~ l1_waybel_0(B_250,A_249)
      | ~ v1_yellow_6(B_250,A_249)
      | ~ v7_waybel_0(B_250)
      | ~ v4_orders_2(B_250)
      | ~ l1_struct_0(A_249)
      | v2_struct_0(A_249)
      | r1_waybel_0(A_251,B_250,C_252)
      | ~ l1_waybel_0(B_250,A_251)
      | v2_struct_0(B_250)
      | ~ l1_struct_0(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_2,c_161])).

tff(c_14,plain,(
    ! [A_15,B_43,C_57,D_64] :
      ( ~ r2_hidden(k2_waybel_0(A_15,B_43,'#skF_2'(A_15,B_43,C_57,D_64)),C_57)
      | r1_waybel_0(A_15,B_43,C_57)
      | ~ m1_subset_1(D_64,u1_struct_0(B_43))
      | ~ l1_waybel_0(B_43,A_15)
      | v2_struct_0(B_43)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_193,plain,(
    ! [A_251,B_250,C_252] :
      ( ~ r2_hidden(k4_yellow_6(A_251,B_250),C_252)
      | r1_waybel_0(A_251,B_250,C_252)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_250)),u1_struct_0(B_250))
      | ~ l1_waybel_0(B_250,A_251)
      | v2_struct_0(B_250)
      | ~ l1_struct_0(A_251)
      | v2_struct_0(A_251)
      | ~ l1_waybel_0(B_250,A_251)
      | ~ v1_yellow_6(B_250,A_251)
      | ~ v7_waybel_0(B_250)
      | ~ v4_orders_2(B_250)
      | ~ l1_struct_0(A_251)
      | v2_struct_0(A_251)
      | r1_waybel_0(A_251,B_250,C_252)
      | ~ l1_waybel_0(B_250,A_251)
      | v2_struct_0(B_250)
      | ~ l1_struct_0(A_251)
      | v2_struct_0(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_14])).

tff(c_199,plain,(
    ! [A_251,B_250,C_252] :
      ( ~ r2_hidden(k4_yellow_6(A_251,B_250),C_252)
      | ~ v1_yellow_6(B_250,A_251)
      | ~ v7_waybel_0(B_250)
      | ~ v4_orders_2(B_250)
      | r1_waybel_0(A_251,B_250,C_252)
      | ~ l1_waybel_0(B_250,A_251)
      | v2_struct_0(B_250)
      | ~ l1_struct_0(A_251)
      | v2_struct_0(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_193])).

tff(c_288,plain,(
    ! [B_303,A_304,A_305,B_306] :
      ( ~ v1_yellow_6(B_303,A_304)
      | ~ v7_waybel_0(B_303)
      | ~ v4_orders_2(B_303)
      | r1_waybel_0(A_304,B_303,'#skF_4'(A_305,B_306,k10_yellow_6(A_305,B_306),k4_yellow_6(A_304,B_303)))
      | ~ l1_waybel_0(B_303,A_304)
      | v2_struct_0(B_303)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304)
      | r2_hidden(k4_yellow_6(A_304,B_303),k10_yellow_6(A_305,B_306))
      | ~ m1_subset_1(k4_yellow_6(A_304,B_303),u1_struct_0(A_305))
      | ~ l1_waybel_0(B_306,A_305)
      | ~ v7_waybel_0(B_306)
      | ~ v4_orders_2(B_306)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(resolution,[status(thm)],[c_207,c_199])).

tff(c_36,plain,(
    ! [A_68,B_112,D_145] :
      ( ~ r1_waybel_0(A_68,B_112,'#skF_4'(A_68,B_112,k10_yellow_6(A_68,B_112),D_145))
      | r2_hidden(D_145,k10_yellow_6(A_68,B_112))
      | ~ m1_subset_1(D_145,u1_struct_0(A_68))
      | ~ m1_subset_1(k10_yellow_6(A_68,B_112),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_waybel_0(B_112,A_68)
      | ~ v7_waybel_0(B_112)
      | ~ v4_orders_2(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_293,plain,(
    ! [A_307,B_308] :
      ( ~ m1_subset_1(k10_yellow_6(A_307,B_308),k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ v1_yellow_6(B_308,A_307)
      | ~ l1_struct_0(A_307)
      | r2_hidden(k4_yellow_6(A_307,B_308),k10_yellow_6(A_307,B_308))
      | ~ m1_subset_1(k4_yellow_6(A_307,B_308),u1_struct_0(A_307))
      | ~ l1_waybel_0(B_308,A_307)
      | ~ v7_waybel_0(B_308)
      | ~ v4_orders_2(B_308)
      | v2_struct_0(B_308)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_288,c_36])).

tff(c_297,plain,(
    ! [B_309,A_310] :
      ( ~ v1_yellow_6(B_309,A_310)
      | ~ l1_struct_0(A_310)
      | r2_hidden(k4_yellow_6(A_310,B_309),k10_yellow_6(A_310,B_309))
      | ~ m1_subset_1(k4_yellow_6(A_310,B_309),u1_struct_0(A_310))
      | ~ l1_waybel_0(B_309,A_310)
      | ~ v7_waybel_0(B_309)
      | ~ v4_orders_2(B_309)
      | v2_struct_0(B_309)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_40,c_293])).

tff(c_46,plain,(
    ~ r2_hidden(k4_yellow_6('#skF_7','#skF_8'),k10_yellow_6('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_303,plain,
    ( ~ v1_yellow_6('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7')
    | ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_297,c_46])).

tff(c_307,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_48,c_50,c_303])).

tff(c_308,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_307])).

tff(c_309,plain,(
    ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_312,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_309])).

tff(c_315,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_312])).

tff(c_316,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_315])).

tff(c_320,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_316])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_320])).

tff(c_325,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_329,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_325])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:17:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  %$ r1_waybel_0 > r1_orders_2 > m1_connsp_2 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_5 > #skF_4 > #skF_8 > #skF_3
% 3.52/1.56  
% 3.52/1.56  %Foreground sorts:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Background operators:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Foreground operators:
% 3.52/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.56  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.52/1.56  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.52/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.56  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.52/1.56  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.52/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.52/1.56  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 3.52/1.56  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.52/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.56  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.52/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.52/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.52/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.52/1.56  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 3.52/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.52/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.52/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.56  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.52/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.52/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.56  
% 3.52/1.58  tff(f_190, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 3.52/1.58  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.52/1.58  tff(f_146, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 3.52/1.58  tff(f_137, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 3.52/1.58  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 3.52/1.58  tff(f_46, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.52/1.58  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.52/1.58  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.52/1.58  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 3.52/1.58  tff(f_168, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k4_yellow_6(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_6)).
% 3.52/1.58  tff(c_58, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.58  tff(c_62, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_48, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_42, plain, (![A_154, B_155]: (m1_subset_1(k4_yellow_6(A_154, B_155), u1_struct_0(A_154)) | ~l1_waybel_0(B_155, A_154) | ~l1_struct_0(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.52/1.58  tff(c_56, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_60, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_54, plain, (v4_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_52, plain, (v7_waybel_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_50, plain, (v1_yellow_6('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_40, plain, (![A_152, B_153]: (m1_subset_1(k10_yellow_6(A_152, B_153), k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_waybel_0(B_153, A_152) | ~v7_waybel_0(B_153) | ~v4_orders_2(B_153) | v2_struct_0(B_153) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.52/1.58  tff(c_141, plain, (![A_227, B_228, D_229]: (m1_connsp_2('#skF_4'(A_227, B_228, k10_yellow_6(A_227, B_228), D_229), A_227, D_229) | r2_hidden(D_229, k10_yellow_6(A_227, B_228)) | ~m1_subset_1(D_229, u1_struct_0(A_227)) | ~m1_subset_1(k10_yellow_6(A_227, B_228), k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_waybel_0(B_228, A_227) | ~v7_waybel_0(B_228) | ~v4_orders_2(B_228) | v2_struct_0(B_228) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.52/1.58  tff(c_145, plain, (![A_230, B_231, D_232]: (m1_connsp_2('#skF_4'(A_230, B_231, k10_yellow_6(A_230, B_231), D_232), A_230, D_232) | r2_hidden(D_232, k10_yellow_6(A_230, B_231)) | ~m1_subset_1(D_232, u1_struct_0(A_230)) | ~l1_waybel_0(B_231, A_230) | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_40, c_141])).
% 3.52/1.58  tff(c_6, plain, (![C_7, A_4, B_5]: (m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_connsp_2(C_7, A_4, B_5) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.58  tff(c_158, plain, (![A_230, B_231, D_232]: (m1_subset_1('#skF_4'(A_230, B_231, k10_yellow_6(A_230, B_231), D_232), k1_zfmisc_1(u1_struct_0(A_230))) | r2_hidden(D_232, k10_yellow_6(A_230, B_231)) | ~m1_subset_1(D_232, u1_struct_0(A_230)) | ~l1_waybel_0(B_231, A_230) | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_145, c_6])).
% 3.52/1.58  tff(c_8, plain, (![C_14, B_12, A_8]: (r2_hidden(C_14, B_12) | ~m1_connsp_2(B_12, A_8, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_8)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.58  tff(c_202, plain, (![D_256, A_257, B_258]: (r2_hidden(D_256, '#skF_4'(A_257, B_258, k10_yellow_6(A_257, B_258), D_256)) | ~m1_subset_1('#skF_4'(A_257, B_258, k10_yellow_6(A_257, B_258), D_256), k1_zfmisc_1(u1_struct_0(A_257))) | r2_hidden(D_256, k10_yellow_6(A_257, B_258)) | ~m1_subset_1(D_256, u1_struct_0(A_257)) | ~l1_waybel_0(B_258, A_257) | ~v7_waybel_0(B_258) | ~v4_orders_2(B_258) | v2_struct_0(B_258) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_145, c_8])).
% 3.52/1.58  tff(c_207, plain, (![D_262, A_263, B_264]: (r2_hidden(D_262, '#skF_4'(A_263, B_264, k10_yellow_6(A_263, B_264), D_262)) | r2_hidden(D_262, k10_yellow_6(A_263, B_264)) | ~m1_subset_1(D_262, u1_struct_0(A_263)) | ~l1_waybel_0(B_264, A_263) | ~v7_waybel_0(B_264) | ~v4_orders_2(B_264) | v2_struct_0(B_264) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(resolution, [status(thm)], [c_158, c_202])).
% 3.52/1.58  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.52/1.58  tff(c_18, plain, (![A_15, B_43, C_57, D_64]: (m1_subset_1('#skF_2'(A_15, B_43, C_57, D_64), u1_struct_0(B_43)) | r1_waybel_0(A_15, B_43, C_57) | ~m1_subset_1(D_64, u1_struct_0(B_43)) | ~l1_waybel_0(B_43, A_15) | v2_struct_0(B_43) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.52/1.58  tff(c_72, plain, (![A_187, B_188, C_189]: (k2_waybel_0(A_187, B_188, C_189)=k4_yellow_6(A_187, B_188) | ~m1_subset_1(C_189, u1_struct_0(B_188)) | ~l1_waybel_0(B_188, A_187) | ~v1_yellow_6(B_188, A_187) | ~v7_waybel_0(B_188) | ~v4_orders_2(B_188) | v2_struct_0(B_188) | ~l1_struct_0(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.58  tff(c_161, plain, (![C_244, D_242, A_241, B_240, A_243]: (k2_waybel_0(A_241, B_240, '#skF_2'(A_243, B_240, C_244, D_242))=k4_yellow_6(A_241, B_240) | ~l1_waybel_0(B_240, A_241) | ~v1_yellow_6(B_240, A_241) | ~v7_waybel_0(B_240) | ~v4_orders_2(B_240) | ~l1_struct_0(A_241) | v2_struct_0(A_241) | r1_waybel_0(A_243, B_240, C_244) | ~m1_subset_1(D_242, u1_struct_0(B_240)) | ~l1_waybel_0(B_240, A_243) | v2_struct_0(B_240) | ~l1_struct_0(A_243) | v2_struct_0(A_243))), inference(resolution, [status(thm)], [c_18, c_72])).
% 3.52/1.58  tff(c_186, plain, (![A_249, B_250, A_251, C_252]: (k2_waybel_0(A_249, B_250, '#skF_2'(A_251, B_250, C_252, '#skF_1'(u1_struct_0(B_250))))=k4_yellow_6(A_249, B_250) | ~l1_waybel_0(B_250, A_249) | ~v1_yellow_6(B_250, A_249) | ~v7_waybel_0(B_250) | ~v4_orders_2(B_250) | ~l1_struct_0(A_249) | v2_struct_0(A_249) | r1_waybel_0(A_251, B_250, C_252) | ~l1_waybel_0(B_250, A_251) | v2_struct_0(B_250) | ~l1_struct_0(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_2, c_161])).
% 3.52/1.58  tff(c_14, plain, (![A_15, B_43, C_57, D_64]: (~r2_hidden(k2_waybel_0(A_15, B_43, '#skF_2'(A_15, B_43, C_57, D_64)), C_57) | r1_waybel_0(A_15, B_43, C_57) | ~m1_subset_1(D_64, u1_struct_0(B_43)) | ~l1_waybel_0(B_43, A_15) | v2_struct_0(B_43) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.52/1.58  tff(c_193, plain, (![A_251, B_250, C_252]: (~r2_hidden(k4_yellow_6(A_251, B_250), C_252) | r1_waybel_0(A_251, B_250, C_252) | ~m1_subset_1('#skF_1'(u1_struct_0(B_250)), u1_struct_0(B_250)) | ~l1_waybel_0(B_250, A_251) | v2_struct_0(B_250) | ~l1_struct_0(A_251) | v2_struct_0(A_251) | ~l1_waybel_0(B_250, A_251) | ~v1_yellow_6(B_250, A_251) | ~v7_waybel_0(B_250) | ~v4_orders_2(B_250) | ~l1_struct_0(A_251) | v2_struct_0(A_251) | r1_waybel_0(A_251, B_250, C_252) | ~l1_waybel_0(B_250, A_251) | v2_struct_0(B_250) | ~l1_struct_0(A_251) | v2_struct_0(A_251))), inference(superposition, [status(thm), theory('equality')], [c_186, c_14])).
% 3.52/1.58  tff(c_199, plain, (![A_251, B_250, C_252]: (~r2_hidden(k4_yellow_6(A_251, B_250), C_252) | ~v1_yellow_6(B_250, A_251) | ~v7_waybel_0(B_250) | ~v4_orders_2(B_250) | r1_waybel_0(A_251, B_250, C_252) | ~l1_waybel_0(B_250, A_251) | v2_struct_0(B_250) | ~l1_struct_0(A_251) | v2_struct_0(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_193])).
% 3.52/1.58  tff(c_288, plain, (![B_303, A_304, A_305, B_306]: (~v1_yellow_6(B_303, A_304) | ~v7_waybel_0(B_303) | ~v4_orders_2(B_303) | r1_waybel_0(A_304, B_303, '#skF_4'(A_305, B_306, k10_yellow_6(A_305, B_306), k4_yellow_6(A_304, B_303))) | ~l1_waybel_0(B_303, A_304) | v2_struct_0(B_303) | ~l1_struct_0(A_304) | v2_struct_0(A_304) | r2_hidden(k4_yellow_6(A_304, B_303), k10_yellow_6(A_305, B_306)) | ~m1_subset_1(k4_yellow_6(A_304, B_303), u1_struct_0(A_305)) | ~l1_waybel_0(B_306, A_305) | ~v7_waybel_0(B_306) | ~v4_orders_2(B_306) | v2_struct_0(B_306) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(resolution, [status(thm)], [c_207, c_199])).
% 3.52/1.58  tff(c_36, plain, (![A_68, B_112, D_145]: (~r1_waybel_0(A_68, B_112, '#skF_4'(A_68, B_112, k10_yellow_6(A_68, B_112), D_145)) | r2_hidden(D_145, k10_yellow_6(A_68, B_112)) | ~m1_subset_1(D_145, u1_struct_0(A_68)) | ~m1_subset_1(k10_yellow_6(A_68, B_112), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_waybel_0(B_112, A_68) | ~v7_waybel_0(B_112) | ~v4_orders_2(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.52/1.58  tff(c_293, plain, (![A_307, B_308]: (~m1_subset_1(k10_yellow_6(A_307, B_308), k1_zfmisc_1(u1_struct_0(A_307))) | ~v1_yellow_6(B_308, A_307) | ~l1_struct_0(A_307) | r2_hidden(k4_yellow_6(A_307, B_308), k10_yellow_6(A_307, B_308)) | ~m1_subset_1(k4_yellow_6(A_307, B_308), u1_struct_0(A_307)) | ~l1_waybel_0(B_308, A_307) | ~v7_waybel_0(B_308) | ~v4_orders_2(B_308) | v2_struct_0(B_308) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307))), inference(resolution, [status(thm)], [c_288, c_36])).
% 3.52/1.58  tff(c_297, plain, (![B_309, A_310]: (~v1_yellow_6(B_309, A_310) | ~l1_struct_0(A_310) | r2_hidden(k4_yellow_6(A_310, B_309), k10_yellow_6(A_310, B_309)) | ~m1_subset_1(k4_yellow_6(A_310, B_309), u1_struct_0(A_310)) | ~l1_waybel_0(B_309, A_310) | ~v7_waybel_0(B_309) | ~v4_orders_2(B_309) | v2_struct_0(B_309) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(resolution, [status(thm)], [c_40, c_293])).
% 3.52/1.58  tff(c_46, plain, (~r2_hidden(k4_yellow_6('#skF_7', '#skF_8'), k10_yellow_6('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 3.52/1.58  tff(c_303, plain, (~v1_yellow_6('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7') | ~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_297, c_46])).
% 3.52/1.58  tff(c_307, plain, (~l1_struct_0('#skF_7') | ~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_48, c_50, c_303])).
% 3.52/1.58  tff(c_308, plain, (~l1_struct_0('#skF_7') | ~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_307])).
% 3.52/1.58  tff(c_309, plain, (~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_308])).
% 3.52/1.58  tff(c_312, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_42, c_309])).
% 3.52/1.58  tff(c_315, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_312])).
% 3.52/1.58  tff(c_316, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_315])).
% 3.52/1.58  tff(c_320, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_4, c_316])).
% 3.52/1.58  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_320])).
% 3.52/1.58  tff(c_325, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_308])).
% 3.52/1.58  tff(c_329, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_4, c_325])).
% 3.52/1.58  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_329])).
% 3.52/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.58  
% 3.52/1.58  Inference rules
% 3.52/1.58  ----------------------
% 3.52/1.58  #Ref     : 0
% 3.52/1.58  #Sup     : 57
% 3.52/1.58  #Fact    : 0
% 3.52/1.58  #Define  : 0
% 3.52/1.58  #Split   : 1
% 3.52/1.58  #Chain   : 0
% 3.52/1.58  #Close   : 0
% 3.52/1.58  
% 3.52/1.58  Ordering : KBO
% 3.52/1.58  
% 3.52/1.58  Simplification rules
% 3.52/1.58  ----------------------
% 3.52/1.58  #Subsume      : 7
% 3.52/1.58  #Demod        : 10
% 3.52/1.58  #Tautology    : 20
% 3.52/1.58  #SimpNegUnit  : 2
% 3.52/1.58  #BackRed      : 0
% 3.52/1.58  
% 3.52/1.58  #Partial instantiations: 0
% 3.52/1.58  #Strategies tried      : 1
% 3.52/1.58  
% 3.52/1.58  Timing (in seconds)
% 3.52/1.58  ----------------------
% 3.52/1.59  Preprocessing        : 0.40
% 3.52/1.59  Parsing              : 0.20
% 3.52/1.59  CNF conversion       : 0.04
% 3.52/1.59  Main loop            : 0.39
% 3.52/1.59  Inferencing          : 0.17
% 3.52/1.59  Reduction            : 0.09
% 3.52/1.59  Demodulation         : 0.06
% 3.52/1.59  BG Simplification    : 0.03
% 3.52/1.59  Subsumption          : 0.07
% 3.52/1.59  Abstraction          : 0.02
% 3.52/1.59  MUC search           : 0.00
% 3.52/1.59  Cooper               : 0.00
% 3.52/1.59  Total                : 0.84
% 3.52/1.59  Index Insertion      : 0.00
% 3.52/1.59  Index Deletion       : 0.00
% 3.52/1.59  Index Matching       : 0.00
% 3.52/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
