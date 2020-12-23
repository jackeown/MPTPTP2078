%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1944+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.30s
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
%$ r1_waybel_0 > r1_orders_2 > m1_connsp_2 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_6

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_189,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

tff(f_98,axiom,(
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

tff(f_80,axiom,(
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

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_167,axiom,(
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

tff(f_128,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_48,axiom,(
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

tff(f_150,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_36,plain,(
    ! [A_142] :
      ( l1_struct_0(A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_48,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_34,plain,(
    ! [A_140,B_141] :
      ( m1_subset_1(k4_yellow_6(A_140,B_141),u1_struct_0(A_140))
      | ~ l1_waybel_0(B_141,A_140)
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_54,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_52,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_50,plain,(
    v1_yellow_6('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_32,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1(k10_yellow_6(A_138,B_139),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_waybel_0(B_139,A_138)
      | ~ v7_waybel_0(B_139)
      | ~ v4_orders_2(B_139)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_136,plain,(
    ! [A_220,B_221,D_222] :
      ( m1_connsp_2('#skF_3'(A_220,B_221,k10_yellow_6(A_220,B_221),D_222),A_220,D_222)
      | r2_hidden(D_222,k10_yellow_6(A_220,B_221))
      | ~ m1_subset_1(D_222,u1_struct_0(A_220))
      | ~ m1_subset_1(k10_yellow_6(A_220,B_221),k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_waybel_0(B_221,A_220)
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_141,plain,(
    ! [A_226,B_227,D_228] :
      ( m1_connsp_2('#skF_3'(A_226,B_227,k10_yellow_6(A_226,B_227),D_228),A_226,D_228)
      | r2_hidden(D_228,k10_yellow_6(A_226,B_227))
      | ~ m1_subset_1(D_228,u1_struct_0(A_226))
      | ~ l1_waybel_0(B_227,A_226)
      | ~ v7_waybel_0(B_227)
      | ~ v4_orders_2(B_227)
      | v2_struct_0(B_227)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_32,c_136])).

tff(c_38,plain,(
    ! [C_146,A_143,B_144] :
      ( m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_connsp_2(C_146,A_143,B_144)
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_150,plain,(
    ! [A_226,B_227,D_228] :
      ( m1_subset_1('#skF_3'(A_226,B_227,k10_yellow_6(A_226,B_227),D_228),k1_zfmisc_1(u1_struct_0(A_226)))
      | r2_hidden(D_228,k10_yellow_6(A_226,B_227))
      | ~ m1_subset_1(D_228,u1_struct_0(A_226))
      | ~ l1_waybel_0(B_227,A_226)
      | ~ v7_waybel_0(B_227)
      | ~ v4_orders_2(B_227)
      | v2_struct_0(B_227)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_141,c_38])).

tff(c_44,plain,(
    ! [C_162,B_160,A_156] :
      ( r2_hidden(C_162,B_160)
      | ~ m1_connsp_2(B_160,A_156,C_162)
      | ~ m1_subset_1(C_162,u1_struct_0(A_156))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_202,plain,(
    ! [D_256,A_257,B_258] :
      ( r2_hidden(D_256,'#skF_3'(A_257,B_258,k10_yellow_6(A_257,B_258),D_256))
      | ~ m1_subset_1('#skF_3'(A_257,B_258,k10_yellow_6(A_257,B_258),D_256),k1_zfmisc_1(u1_struct_0(A_257)))
      | r2_hidden(D_256,k10_yellow_6(A_257,B_258))
      | ~ m1_subset_1(D_256,u1_struct_0(A_257))
      | ~ l1_waybel_0(B_258,A_257)
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_141,c_44])).

tff(c_207,plain,(
    ! [D_262,A_263,B_264] :
      ( r2_hidden(D_262,'#skF_3'(A_263,B_264,k10_yellow_6(A_263,B_264),D_262))
      | r2_hidden(D_262,k10_yellow_6(A_263,B_264))
      | ~ m1_subset_1(D_262,u1_struct_0(A_263))
      | ~ l1_waybel_0(B_264,A_263)
      | ~ v7_waybel_0(B_264)
      | ~ v4_orders_2(B_264)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(resolution,[status(thm)],[c_150,c_202])).

tff(c_40,plain,(
    ! [A_147] : m1_subset_1('#skF_6'(A_147),A_147) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_1,B_29,C_43,D_50] :
      ( m1_subset_1('#skF_1'(A_1,B_29,C_43,D_50),u1_struct_0(B_29))
      | r1_waybel_0(A_1,B_29,C_43)
      | ~ m1_subset_1(D_50,u1_struct_0(B_29))
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    ! [A_191,B_192,C_193] :
      ( k2_waybel_0(A_191,B_192,C_193) = k4_yellow_6(A_191,B_192)
      | ~ m1_subset_1(C_193,u1_struct_0(B_192))
      | ~ l1_waybel_0(B_192,A_191)
      | ~ v1_yellow_6(B_192,A_191)
      | ~ v7_waybel_0(B_192)
      | ~ v4_orders_2(B_192)
      | v2_struct_0(B_192)
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_161,plain,(
    ! [A_241,A_244,B_243,C_242,D_240] :
      ( k2_waybel_0(A_241,B_243,'#skF_1'(A_244,B_243,C_242,D_240)) = k4_yellow_6(A_241,B_243)
      | ~ l1_waybel_0(B_243,A_241)
      | ~ v1_yellow_6(B_243,A_241)
      | ~ v7_waybel_0(B_243)
      | ~ v4_orders_2(B_243)
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241)
      | r1_waybel_0(A_244,B_243,C_242)
      | ~ m1_subset_1(D_240,u1_struct_0(B_243))
      | ~ l1_waybel_0(B_243,A_244)
      | v2_struct_0(B_243)
      | ~ l1_struct_0(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_186,plain,(
    ! [A_249,B_250,A_251,C_252] :
      ( k2_waybel_0(A_249,B_250,'#skF_1'(A_251,B_250,C_252,'#skF_6'(u1_struct_0(B_250)))) = k4_yellow_6(A_249,B_250)
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
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_6,plain,(
    ! [A_1,B_29,C_43,D_50] :
      ( ~ r2_hidden(k2_waybel_0(A_1,B_29,'#skF_1'(A_1,B_29,C_43,D_50)),C_43)
      | r1_waybel_0(A_1,B_29,C_43)
      | ~ m1_subset_1(D_50,u1_struct_0(B_29))
      | ~ l1_waybel_0(B_29,A_1)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,(
    ! [A_251,B_250,C_252] :
      ( ~ r2_hidden(k4_yellow_6(A_251,B_250),C_252)
      | r1_waybel_0(A_251,B_250,C_252)
      | ~ m1_subset_1('#skF_6'(u1_struct_0(B_250)),u1_struct_0(B_250))
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
    inference(superposition,[status(thm),theory(equality)],[c_186,c_6])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_193])).

tff(c_288,plain,(
    ! [B_303,A_304,A_305,B_306] :
      ( ~ v1_yellow_6(B_303,A_304)
      | ~ v7_waybel_0(B_303)
      | ~ v4_orders_2(B_303)
      | r1_waybel_0(A_304,B_303,'#skF_3'(A_305,B_306,k10_yellow_6(A_305,B_306),k4_yellow_6(A_304,B_303)))
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

tff(c_28,plain,(
    ! [A_54,B_98,D_131] :
      ( ~ r1_waybel_0(A_54,B_98,'#skF_3'(A_54,B_98,k10_yellow_6(A_54,B_98),D_131))
      | r2_hidden(D_131,k10_yellow_6(A_54,B_98))
      | ~ m1_subset_1(D_131,u1_struct_0(A_54))
      | ~ m1_subset_1(k10_yellow_6(A_54,B_98),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_waybel_0(B_98,A_54)
      | ~ v7_waybel_0(B_98)
      | ~ v4_orders_2(B_98)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

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
    inference(resolution,[status(thm)],[c_288,c_28])).

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
    inference(resolution,[status(thm)],[c_32,c_293])).

tff(c_46,plain,(
    ~ r2_hidden(k4_yellow_6('#skF_7','#skF_8'),k10_yellow_6('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

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
    inference(resolution,[status(thm)],[c_34,c_309])).

tff(c_315,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_312])).

tff(c_316,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_315])).

tff(c_320,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_316])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_320])).

tff(c_325,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_329,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_325])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_329])).

%------------------------------------------------------------------------------
