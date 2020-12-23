%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1944+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 249 expanded)
%              Number of leaves         :   39 ( 106 expanded)
%              Depth                    :   21
%              Number of atoms          :  542 (1845 expanded)
%              Number of equality atoms :    6 (  25 expanded)
%              Maximal formula depth    :   29 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > m1_connsp_2 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > o_2_6_yellow_6 > k4_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

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

tff(o_2_6_yellow_6,type,(
    o_2_6_yellow_6: ( $i * $i ) > $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
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

tff(f_184,axiom,(
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

tff(f_167,axiom,(
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

tff(f_145,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & v1_yellow_6(B,A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_6_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_6_yellow_6)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_58,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_36,plain,(
    ! [A_142] :
      ( l1_struct_0(A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_34,plain,(
    ! [A_140,B_141] :
      ( m1_subset_1(k4_yellow_6(A_140,B_141),u1_struct_0(A_140))
      | ~ l1_waybel_0(B_141,A_140)
      | ~ l1_struct_0(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

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

tff(c_135,plain,(
    ! [A_222,B_223,D_224] :
      ( m1_connsp_2('#skF_3'(A_222,B_223,k10_yellow_6(A_222,B_223),D_224),A_222,D_224)
      | r2_hidden(D_224,k10_yellow_6(A_222,B_223))
      | ~ m1_subset_1(D_224,u1_struct_0(A_222))
      | ~ m1_subset_1(k10_yellow_6(A_222,B_223),k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_waybel_0(B_223,A_222)
      | ~ v7_waybel_0(B_223)
      | ~ v4_orders_2(B_223)
      | v2_struct_0(B_223)
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_143,plain,(
    ! [A_229,B_230,D_231] :
      ( m1_connsp_2('#skF_3'(A_229,B_230,k10_yellow_6(A_229,B_230),D_231),A_229,D_231)
      | r2_hidden(D_231,k10_yellow_6(A_229,B_230))
      | ~ m1_subset_1(D_231,u1_struct_0(A_229))
      | ~ l1_waybel_0(B_230,A_229)
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_38,plain,(
    ! [C_146,A_143,B_144] :
      ( m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_connsp_2(C_146,A_143,B_144)
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_156,plain,(
    ! [A_229,B_230,D_231] :
      ( m1_subset_1('#skF_3'(A_229,B_230,k10_yellow_6(A_229,B_230),D_231),k1_zfmisc_1(u1_struct_0(A_229)))
      | r2_hidden(D_231,k10_yellow_6(A_229,B_230))
      | ~ m1_subset_1(D_231,u1_struct_0(A_229))
      | ~ l1_waybel_0(B_230,A_229)
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_143,c_38])).

tff(c_44,plain,(
    ! [C_162,B_160,A_156] :
      ( r2_hidden(C_162,B_160)
      | ~ m1_connsp_2(B_160,A_156,C_162)
      | ~ m1_subset_1(C_162,u1_struct_0(A_156))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_184,plain,(
    ! [D_251,A_252,B_253] :
      ( r2_hidden(D_251,'#skF_3'(A_252,B_253,k10_yellow_6(A_252,B_253),D_251))
      | ~ m1_subset_1('#skF_3'(A_252,B_253,k10_yellow_6(A_252,B_253),D_251),k1_zfmisc_1(u1_struct_0(A_252)))
      | r2_hidden(D_251,k10_yellow_6(A_252,B_253))
      | ~ m1_subset_1(D_251,u1_struct_0(A_252))
      | ~ l1_waybel_0(B_253,A_252)
      | ~ v7_waybel_0(B_253)
      | ~ v4_orders_2(B_253)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(resolution,[status(thm)],[c_143,c_44])).

tff(c_187,plain,(
    ! [D_231,A_229,B_230] :
      ( r2_hidden(D_231,'#skF_3'(A_229,B_230,k10_yellow_6(A_229,B_230),D_231))
      | r2_hidden(D_231,k10_yellow_6(A_229,B_230))
      | ~ m1_subset_1(D_231,u1_struct_0(A_229))
      | ~ l1_waybel_0(B_230,A_229)
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_156,c_184])).

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
    ! [A_192,B_193,C_194] :
      ( k2_waybel_0(A_192,B_193,C_194) = k4_yellow_6(A_192,B_193)
      | ~ m1_subset_1(C_194,u1_struct_0(B_193))
      | ~ l1_waybel_0(B_193,A_192)
      | ~ v1_yellow_6(B_193,A_192)
      | ~ v7_waybel_0(B_193)
      | ~ v4_orders_2(B_193)
      | v2_struct_0(B_193)
      | ~ l1_struct_0(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_160,plain,(
    ! [D_242,A_246,B_244,A_245,C_243] :
      ( k2_waybel_0(A_245,B_244,'#skF_1'(A_246,B_244,C_243,D_242)) = k4_yellow_6(A_245,B_244)
      | ~ l1_waybel_0(B_244,A_245)
      | ~ v1_yellow_6(B_244,A_245)
      | ~ v7_waybel_0(B_244)
      | ~ v4_orders_2(B_244)
      | ~ l1_struct_0(A_245)
      | v2_struct_0(A_245)
      | r1_waybel_0(A_246,B_244,C_243)
      | ~ m1_subset_1(D_242,u1_struct_0(B_244))
      | ~ l1_waybel_0(B_244,A_246)
      | v2_struct_0(B_244)
      | ~ l1_struct_0(A_246)
      | v2_struct_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_190,plain,(
    ! [A_263,A_261,C_260,A_262,B_264] :
      ( k2_waybel_0(A_262,A_263,'#skF_1'(A_261,A_263,C_260,k4_yellow_6(A_263,B_264))) = k4_yellow_6(A_262,A_263)
      | ~ l1_waybel_0(A_263,A_262)
      | ~ v1_yellow_6(A_263,A_262)
      | ~ v7_waybel_0(A_263)
      | ~ v4_orders_2(A_263)
      | ~ l1_struct_0(A_262)
      | v2_struct_0(A_262)
      | r1_waybel_0(A_261,A_263,C_260)
      | ~ l1_waybel_0(A_263,A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261)
      | ~ l1_waybel_0(B_264,A_263)
      | ~ l1_struct_0(A_263)
      | v2_struct_0(A_263) ) ),
    inference(resolution,[status(thm)],[c_34,c_160])).

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

tff(c_266,plain,(
    ! [A_304,A_305,C_306,B_307] :
      ( ~ r2_hidden(k4_yellow_6(A_304,A_305),C_306)
      | r1_waybel_0(A_304,A_305,C_306)
      | ~ m1_subset_1(k4_yellow_6(A_305,B_307),u1_struct_0(A_305))
      | ~ l1_waybel_0(A_305,A_304)
      | v2_struct_0(A_305)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304)
      | ~ l1_waybel_0(A_305,A_304)
      | ~ v1_yellow_6(A_305,A_304)
      | ~ v7_waybel_0(A_305)
      | ~ v4_orders_2(A_305)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304)
      | r1_waybel_0(A_304,A_305,C_306)
      | ~ l1_waybel_0(A_305,A_304)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304)
      | ~ l1_waybel_0(B_307,A_305)
      | ~ l1_struct_0(A_305)
      | v2_struct_0(A_305) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_6])).

tff(c_428,plain,(
    ! [A_375,B_374,B_378,A_377,A_376] :
      ( ~ m1_subset_1(k4_yellow_6(A_376,B_378),u1_struct_0(A_376))
      | ~ v1_yellow_6(A_376,A_377)
      | ~ v7_waybel_0(A_376)
      | ~ v4_orders_2(A_376)
      | r1_waybel_0(A_377,A_376,'#skF_3'(A_375,B_374,k10_yellow_6(A_375,B_374),k4_yellow_6(A_377,A_376)))
      | ~ l1_waybel_0(A_376,A_377)
      | ~ l1_struct_0(A_377)
      | v2_struct_0(A_377)
      | ~ l1_waybel_0(B_378,A_376)
      | ~ l1_struct_0(A_376)
      | v2_struct_0(A_376)
      | r2_hidden(k4_yellow_6(A_377,A_376),k10_yellow_6(A_375,B_374))
      | ~ m1_subset_1(k4_yellow_6(A_377,A_376),u1_struct_0(A_375))
      | ~ l1_waybel_0(B_374,A_375)
      | ~ v7_waybel_0(B_374)
      | ~ v4_orders_2(B_374)
      | v2_struct_0(B_374)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(resolution,[status(thm)],[c_187,c_266])).

tff(c_432,plain,(
    ! [A_380,B_383,A_381,A_379,B_382] :
      ( ~ v1_yellow_6(A_381,A_380)
      | ~ v7_waybel_0(A_381)
      | ~ v4_orders_2(A_381)
      | r1_waybel_0(A_380,A_381,'#skF_3'(A_379,B_382,k10_yellow_6(A_379,B_382),k4_yellow_6(A_380,A_381)))
      | ~ l1_waybel_0(A_381,A_380)
      | ~ l1_struct_0(A_380)
      | v2_struct_0(A_380)
      | r2_hidden(k4_yellow_6(A_380,A_381),k10_yellow_6(A_379,B_382))
      | ~ m1_subset_1(k4_yellow_6(A_380,A_381),u1_struct_0(A_379))
      | ~ l1_waybel_0(B_382,A_379)
      | ~ v7_waybel_0(B_382)
      | ~ v4_orders_2(B_382)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379)
      | ~ l1_waybel_0(B_383,A_381)
      | ~ l1_struct_0(A_381)
      | v2_struct_0(A_381) ) ),
    inference(resolution,[status(thm)],[c_34,c_428])).

tff(c_434,plain,(
    ! [A_380,A_379,B_382] :
      ( ~ v1_yellow_6('#skF_6',A_380)
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | r1_waybel_0(A_380,'#skF_6','#skF_3'(A_379,B_382,k10_yellow_6(A_379,B_382),k4_yellow_6(A_380,'#skF_6')))
      | ~ l1_waybel_0('#skF_6',A_380)
      | ~ l1_struct_0(A_380)
      | v2_struct_0(A_380)
      | r2_hidden(k4_yellow_6(A_380,'#skF_6'),k10_yellow_6(A_379,B_382))
      | ~ m1_subset_1(k4_yellow_6(A_380,'#skF_6'),u1_struct_0(A_379))
      | ~ l1_waybel_0(B_382,A_379)
      | ~ v7_waybel_0(B_382)
      | ~ v4_orders_2(B_382)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379)
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_432])).

tff(c_437,plain,(
    ! [A_380,A_379,B_382] :
      ( ~ v1_yellow_6('#skF_6',A_380)
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | r1_waybel_0(A_380,'#skF_6','#skF_3'(A_379,B_382,k10_yellow_6(A_379,B_382),k4_yellow_6(A_380,'#skF_6')))
      | ~ l1_waybel_0('#skF_6',A_380)
      | ~ l1_struct_0(A_380)
      | v2_struct_0(A_380)
      | r2_hidden(k4_yellow_6(A_380,'#skF_6'),k10_yellow_6(A_379,B_382))
      | ~ m1_subset_1(k4_yellow_6(A_380,'#skF_6'),u1_struct_0(A_379))
      | ~ l1_waybel_0(B_382,A_379)
      | ~ v7_waybel_0(B_382)
      | ~ v4_orders_2(B_382)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379)
      | ~ l1_struct_0('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_434])).

tff(c_438,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_441,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_438])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_441])).

tff(c_447,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_60,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    v1_yellow_6('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_54,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_52,plain,(
    v7_waybel_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_40,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1(o_2_6_yellow_6(A_147,B_148),u1_struct_0(B_148))
      | ~ l1_waybel_0(B_148,A_147)
      | ~ v1_yellow_6(B_148,A_147)
      | ~ v7_waybel_0(B_148)
      | ~ v4_orders_2(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_210,plain,(
    ! [A_269,A_272,C_270,A_273,B_271] :
      ( k2_waybel_0(A_273,B_271,'#skF_1'(A_272,B_271,C_270,o_2_6_yellow_6(A_269,B_271))) = k4_yellow_6(A_273,B_271)
      | ~ l1_waybel_0(B_271,A_273)
      | ~ v1_yellow_6(B_271,A_273)
      | ~ l1_struct_0(A_273)
      | v2_struct_0(A_273)
      | r1_waybel_0(A_272,B_271,C_270)
      | ~ l1_waybel_0(B_271,A_272)
      | ~ l1_struct_0(A_272)
      | v2_struct_0(A_272)
      | ~ l1_waybel_0(B_271,A_269)
      | ~ v1_yellow_6(B_271,A_269)
      | ~ v7_waybel_0(B_271)
      | ~ v4_orders_2(B_271)
      | v2_struct_0(B_271)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_40,c_160])).

tff(c_296,plain,(
    ! [A_326,B_327,C_328,A_329] :
      ( ~ r2_hidden(k4_yellow_6(A_326,B_327),C_328)
      | r1_waybel_0(A_326,B_327,C_328)
      | ~ m1_subset_1(o_2_6_yellow_6(A_329,B_327),u1_struct_0(B_327))
      | ~ l1_waybel_0(B_327,A_326)
      | v2_struct_0(B_327)
      | ~ l1_struct_0(A_326)
      | v2_struct_0(A_326)
      | ~ l1_waybel_0(B_327,A_326)
      | ~ v1_yellow_6(B_327,A_326)
      | ~ l1_struct_0(A_326)
      | v2_struct_0(A_326)
      | r1_waybel_0(A_326,B_327,C_328)
      | ~ l1_waybel_0(B_327,A_326)
      | ~ l1_struct_0(A_326)
      | v2_struct_0(A_326)
      | ~ l1_waybel_0(B_327,A_329)
      | ~ v1_yellow_6(B_327,A_329)
      | ~ v7_waybel_0(B_327)
      | ~ v4_orders_2(B_327)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_6])).

tff(c_508,plain,(
    ! [A_409,B_410,A_408,A_407,B_406] :
      ( ~ m1_subset_1(o_2_6_yellow_6(A_407,B_410),u1_struct_0(B_410))
      | ~ v1_yellow_6(B_410,A_409)
      | r1_waybel_0(A_409,B_410,'#skF_3'(A_408,B_406,k10_yellow_6(A_408,B_406),k4_yellow_6(A_409,B_410)))
      | ~ l1_waybel_0(B_410,A_409)
      | ~ l1_struct_0(A_409)
      | v2_struct_0(A_409)
      | ~ l1_waybel_0(B_410,A_407)
      | ~ v1_yellow_6(B_410,A_407)
      | ~ v7_waybel_0(B_410)
      | ~ v4_orders_2(B_410)
      | v2_struct_0(B_410)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407)
      | r2_hidden(k4_yellow_6(A_409,B_410),k10_yellow_6(A_408,B_406))
      | ~ m1_subset_1(k4_yellow_6(A_409,B_410),u1_struct_0(A_408))
      | ~ l1_waybel_0(B_406,A_408)
      | ~ v7_waybel_0(B_406)
      | ~ v4_orders_2(B_406)
      | v2_struct_0(B_406)
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_187,c_296])).

tff(c_512,plain,(
    ! [B_415,A_414,A_411,B_412,A_413] :
      ( ~ v1_yellow_6(B_412,A_413)
      | r1_waybel_0(A_413,B_412,'#skF_3'(A_414,B_415,k10_yellow_6(A_414,B_415),k4_yellow_6(A_413,B_412)))
      | ~ l1_waybel_0(B_412,A_413)
      | ~ l1_struct_0(A_413)
      | v2_struct_0(A_413)
      | r2_hidden(k4_yellow_6(A_413,B_412),k10_yellow_6(A_414,B_415))
      | ~ m1_subset_1(k4_yellow_6(A_413,B_412),u1_struct_0(A_414))
      | ~ l1_waybel_0(B_415,A_414)
      | ~ v7_waybel_0(B_415)
      | ~ v4_orders_2(B_415)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414)
      | ~ l1_waybel_0(B_412,A_411)
      | ~ v1_yellow_6(B_412,A_411)
      | ~ v7_waybel_0(B_412)
      | ~ v4_orders_2(B_412)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_40,c_508])).

tff(c_514,plain,(
    ! [A_413,A_414,B_415] :
      ( ~ v1_yellow_6('#skF_7',A_413)
      | r1_waybel_0(A_413,'#skF_7','#skF_3'(A_414,B_415,k10_yellow_6(A_414,B_415),k4_yellow_6(A_413,'#skF_7')))
      | ~ l1_waybel_0('#skF_7',A_413)
      | ~ l1_struct_0(A_413)
      | v2_struct_0(A_413)
      | r2_hidden(k4_yellow_6(A_413,'#skF_7'),k10_yellow_6(A_414,B_415))
      | ~ m1_subset_1(k4_yellow_6(A_413,'#skF_7'),u1_struct_0(A_414))
      | ~ l1_waybel_0(B_415,A_414)
      | ~ v7_waybel_0(B_415)
      | ~ v4_orders_2(B_415)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414)
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_512])).

tff(c_517,plain,(
    ! [A_413,A_414,B_415] :
      ( ~ v1_yellow_6('#skF_7',A_413)
      | r1_waybel_0(A_413,'#skF_7','#skF_3'(A_414,B_415,k10_yellow_6(A_414,B_415),k4_yellow_6(A_413,'#skF_7')))
      | ~ l1_waybel_0('#skF_7',A_413)
      | ~ l1_struct_0(A_413)
      | v2_struct_0(A_413)
      | r2_hidden(k4_yellow_6(A_413,'#skF_7'),k10_yellow_6(A_414,B_415))
      | ~ m1_subset_1(k4_yellow_6(A_413,'#skF_7'),u1_struct_0(A_414))
      | ~ l1_waybel_0(B_415,A_414)
      | ~ v7_waybel_0(B_415)
      | ~ v4_orders_2(B_415)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_48,c_514])).

tff(c_519,plain,(
    ! [A_416,A_417,B_418] :
      ( ~ v1_yellow_6('#skF_7',A_416)
      | r1_waybel_0(A_416,'#skF_7','#skF_3'(A_417,B_418,k10_yellow_6(A_417,B_418),k4_yellow_6(A_416,'#skF_7')))
      | ~ l1_waybel_0('#skF_7',A_416)
      | ~ l1_struct_0(A_416)
      | v2_struct_0(A_416)
      | r2_hidden(k4_yellow_6(A_416,'#skF_7'),k10_yellow_6(A_417,B_418))
      | ~ m1_subset_1(k4_yellow_6(A_416,'#skF_7'),u1_struct_0(A_417))
      | ~ l1_waybel_0(B_418,A_417)
      | ~ v7_waybel_0(B_418)
      | ~ v4_orders_2(B_418)
      | v2_struct_0(B_418)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_517])).

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

tff(c_522,plain,(
    ! [A_417] :
      ( ~ m1_subset_1(k10_yellow_6(A_417,'#skF_7'),k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ v1_yellow_6('#skF_7',A_417)
      | ~ l1_struct_0(A_417)
      | r2_hidden(k4_yellow_6(A_417,'#skF_7'),k10_yellow_6(A_417,'#skF_7'))
      | ~ m1_subset_1(k4_yellow_6(A_417,'#skF_7'),u1_struct_0(A_417))
      | ~ l1_waybel_0('#skF_7',A_417)
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(resolution,[status(thm)],[c_519,c_28])).

tff(c_525,plain,(
    ! [A_417] :
      ( ~ m1_subset_1(k10_yellow_6(A_417,'#skF_7'),k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ v1_yellow_6('#skF_7',A_417)
      | ~ l1_struct_0(A_417)
      | r2_hidden(k4_yellow_6(A_417,'#skF_7'),k10_yellow_6(A_417,'#skF_7'))
      | ~ m1_subset_1(k4_yellow_6(A_417,'#skF_7'),u1_struct_0(A_417))
      | ~ l1_waybel_0('#skF_7',A_417)
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_522])).

tff(c_527,plain,(
    ! [A_419] :
      ( ~ m1_subset_1(k10_yellow_6(A_419,'#skF_7'),k1_zfmisc_1(u1_struct_0(A_419)))
      | ~ v1_yellow_6('#skF_7',A_419)
      | ~ l1_struct_0(A_419)
      | r2_hidden(k4_yellow_6(A_419,'#skF_7'),k10_yellow_6(A_419,'#skF_7'))
      | ~ m1_subset_1(k4_yellow_6(A_419,'#skF_7'),u1_struct_0(A_419))
      | ~ l1_waybel_0('#skF_7',A_419)
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_525])).

tff(c_531,plain,(
    ! [A_138] :
      ( ~ v1_yellow_6('#skF_7',A_138)
      | ~ l1_struct_0(A_138)
      | r2_hidden(k4_yellow_6(A_138,'#skF_7'),k10_yellow_6(A_138,'#skF_7'))
      | ~ m1_subset_1(k4_yellow_6(A_138,'#skF_7'),u1_struct_0(A_138))
      | ~ l1_waybel_0('#skF_7',A_138)
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_32,c_527])).

tff(c_534,plain,(
    ! [A_138] :
      ( ~ v1_yellow_6('#skF_7',A_138)
      | ~ l1_struct_0(A_138)
      | r2_hidden(k4_yellow_6(A_138,'#skF_7'),k10_yellow_6(A_138,'#skF_7'))
      | ~ m1_subset_1(k4_yellow_6(A_138,'#skF_7'),u1_struct_0(A_138))
      | ~ l1_waybel_0('#skF_7',A_138)
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_531])).

tff(c_541,plain,(
    ! [A_424] :
      ( ~ v1_yellow_6('#skF_7',A_424)
      | ~ l1_struct_0(A_424)
      | r2_hidden(k4_yellow_6(A_424,'#skF_7'),k10_yellow_6(A_424,'#skF_7'))
      | ~ m1_subset_1(k4_yellow_6(A_424,'#skF_7'),u1_struct_0(A_424))
      | ~ l1_waybel_0('#skF_7',A_424)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_534])).

tff(c_46,plain,(
    ~ r2_hidden(k4_yellow_6('#skF_6','#skF_7'),k10_yellow_6('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_552,plain,
    ( ~ v1_yellow_6('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | ~ m1_subset_1(k4_yellow_6('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_541,c_46])).

tff(c_571,plain,
    ( ~ m1_subset_1(k4_yellow_6('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_447,c_50,c_552])).

tff(c_572,plain,(
    ~ m1_subset_1(k4_yellow_6('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_571])).

tff(c_575,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_572])).

tff(c_578,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_48,c_575])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_578])).

%------------------------------------------------------------------------------
