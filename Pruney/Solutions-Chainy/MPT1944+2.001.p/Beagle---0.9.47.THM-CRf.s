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
% DateTime   : Thu Dec  3 10:30:54 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 187 expanded)
%              Number of leaves         :   39 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  349 (1066 expanded)
%              Number of equality atoms :    6 (  17 expanded)
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

tff(f_195,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_173,axiom,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_151,axiom,(
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

tff(f_133,axiom,(
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

tff(c_58,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    v1_yellow_6('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_72,plain,(
    ! [A_189,B_190,C_191] :
      ( k2_waybel_0(A_189,B_190,C_191) = k4_yellow_6(A_189,B_190)
      | ~ m1_subset_1(C_191,u1_struct_0(B_190))
      | ~ l1_waybel_0(B_190,A_189)
      | ~ v1_yellow_6(B_190,A_189)
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | ~ l1_struct_0(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_87,plain,(
    ! [A_196,B_197] :
      ( k2_waybel_0(A_196,B_197,'#skF_1'(u1_struct_0(B_197))) = k4_yellow_6(A_196,B_197)
      | ~ l1_waybel_0(B_197,A_196)
      | ~ v1_yellow_6(B_197,A_196)
      | ~ v7_waybel_0(B_197)
      | ~ v4_orders_2(B_197)
      | v2_struct_0(B_197)
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_20,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k2_waybel_0(A_68,B_69,C_70),u1_struct_0(A_68))
      | ~ m1_subset_1(C_70,u1_struct_0(B_69))
      | ~ l1_waybel_0(B_69,A_68)
      | v2_struct_0(B_69)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_93,plain,(
    ! [A_196,B_197] :
      ( m1_subset_1(k4_yellow_6(A_196,B_197),u1_struct_0(A_196))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_197)),u1_struct_0(B_197))
      | ~ l1_waybel_0(B_197,A_196)
      | v2_struct_0(B_197)
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196)
      | ~ l1_waybel_0(B_197,A_196)
      | ~ v1_yellow_6(B_197,A_196)
      | ~ v7_waybel_0(B_197)
      | ~ v4_orders_2(B_197)
      | v2_struct_0(B_197)
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_20])).

tff(c_99,plain,(
    ! [A_196,B_197] :
      ( m1_subset_1(k4_yellow_6(A_196,B_197),u1_struct_0(A_196))
      | ~ l1_waybel_0(B_197,A_196)
      | ~ v1_yellow_6(B_197,A_196)
      | ~ v7_waybel_0(B_197)
      | ~ v4_orders_2(B_197)
      | v2_struct_0(B_197)
      | ~ l1_struct_0(A_196)
      | v2_struct_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_60,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_42,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1(k10_yellow_6(A_155,B_156),k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_waybel_0(B_156,A_155)
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_186,plain,(
    ! [A_231,B_232,D_233] :
      ( m1_connsp_2('#skF_4'(A_231,B_232,k10_yellow_6(A_231,B_232),D_233),A_231,D_233)
      | r2_hidden(D_233,k10_yellow_6(A_231,B_232))
      | ~ m1_subset_1(D_233,u1_struct_0(A_231))
      | ~ m1_subset_1(k10_yellow_6(A_231,B_232),k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_waybel_0(B_232,A_231)
      | ~ v7_waybel_0(B_232)
      | ~ v4_orders_2(B_232)
      | v2_struct_0(B_232)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_190,plain,(
    ! [A_234,B_235,D_236] :
      ( m1_connsp_2('#skF_4'(A_234,B_235,k10_yellow_6(A_234,B_235),D_236),A_234,D_236)
      | r2_hidden(D_236,k10_yellow_6(A_234,B_235))
      | ~ m1_subset_1(D_236,u1_struct_0(A_234))
      | ~ l1_waybel_0(B_235,A_234)
      | ~ v7_waybel_0(B_235)
      | ~ v4_orders_2(B_235)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_42,c_186])).

tff(c_6,plain,(
    ! [C_7,A_4,B_5] :
      ( m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_connsp_2(C_7,A_4,B_5)
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_199,plain,(
    ! [A_234,B_235,D_236] :
      ( m1_subset_1('#skF_4'(A_234,B_235,k10_yellow_6(A_234,B_235),D_236),k1_zfmisc_1(u1_struct_0(A_234)))
      | r2_hidden(D_236,k10_yellow_6(A_234,B_235))
      | ~ m1_subset_1(D_236,u1_struct_0(A_234))
      | ~ l1_waybel_0(B_235,A_234)
      | ~ v7_waybel_0(B_235)
      | ~ v4_orders_2(B_235)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_190,c_6])).

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

tff(c_258,plain,(
    ! [D_267,A_268,B_269] :
      ( r2_hidden(D_267,'#skF_4'(A_268,B_269,k10_yellow_6(A_268,B_269),D_267))
      | ~ m1_subset_1('#skF_4'(A_268,B_269,k10_yellow_6(A_268,B_269),D_267),k1_zfmisc_1(u1_struct_0(A_268)))
      | r2_hidden(D_267,k10_yellow_6(A_268,B_269))
      | ~ m1_subset_1(D_267,u1_struct_0(A_268))
      | ~ l1_waybel_0(B_269,A_268)
      | ~ v7_waybel_0(B_269)
      | ~ v4_orders_2(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(resolution,[status(thm)],[c_190,c_8])).

tff(c_262,plain,(
    ! [D_270,A_271,B_272] :
      ( r2_hidden(D_270,'#skF_4'(A_271,B_272,k10_yellow_6(A_271,B_272),D_270))
      | r2_hidden(D_270,k10_yellow_6(A_271,B_272))
      | ~ m1_subset_1(D_270,u1_struct_0(A_271))
      | ~ l1_waybel_0(B_272,A_271)
      | ~ v7_waybel_0(B_272)
      | ~ v4_orders_2(B_272)
      | v2_struct_0(B_272)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_199,c_258])).

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

tff(c_211,plain,(
    ! [C_255,B_251,A_254,A_253,D_252] :
      ( k2_waybel_0(A_253,B_251,'#skF_2'(A_254,B_251,C_255,D_252)) = k4_yellow_6(A_253,B_251)
      | ~ l1_waybel_0(B_251,A_253)
      | ~ v1_yellow_6(B_251,A_253)
      | ~ v7_waybel_0(B_251)
      | ~ v4_orders_2(B_251)
      | ~ l1_struct_0(A_253)
      | v2_struct_0(A_253)
      | r1_waybel_0(A_254,B_251,C_255)
      | ~ m1_subset_1(D_252,u1_struct_0(B_251))
      | ~ l1_waybel_0(B_251,A_254)
      | v2_struct_0(B_251)
      | ~ l1_struct_0(A_254)
      | v2_struct_0(A_254) ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_231,plain,(
    ! [A_256,B_257,A_258,C_259] :
      ( k2_waybel_0(A_256,B_257,'#skF_2'(A_258,B_257,C_259,'#skF_1'(u1_struct_0(B_257)))) = k4_yellow_6(A_256,B_257)
      | ~ l1_waybel_0(B_257,A_256)
      | ~ v1_yellow_6(B_257,A_256)
      | ~ v7_waybel_0(B_257)
      | ~ v4_orders_2(B_257)
      | ~ l1_struct_0(A_256)
      | v2_struct_0(A_256)
      | r1_waybel_0(A_258,B_257,C_259)
      | ~ l1_waybel_0(B_257,A_258)
      | v2_struct_0(B_257)
      | ~ l1_struct_0(A_258)
      | v2_struct_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_2,c_211])).

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

tff(c_238,plain,(
    ! [A_258,B_257,C_259] :
      ( ~ r2_hidden(k4_yellow_6(A_258,B_257),C_259)
      | r1_waybel_0(A_258,B_257,C_259)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_257)),u1_struct_0(B_257))
      | ~ l1_waybel_0(B_257,A_258)
      | v2_struct_0(B_257)
      | ~ l1_struct_0(A_258)
      | v2_struct_0(A_258)
      | ~ l1_waybel_0(B_257,A_258)
      | ~ v1_yellow_6(B_257,A_258)
      | ~ v7_waybel_0(B_257)
      | ~ v4_orders_2(B_257)
      | ~ l1_struct_0(A_258)
      | v2_struct_0(A_258)
      | r1_waybel_0(A_258,B_257,C_259)
      | ~ l1_waybel_0(B_257,A_258)
      | v2_struct_0(B_257)
      | ~ l1_struct_0(A_258)
      | v2_struct_0(A_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_14])).

tff(c_247,plain,(
    ! [A_258,B_257,C_259] :
      ( ~ r2_hidden(k4_yellow_6(A_258,B_257),C_259)
      | ~ v1_yellow_6(B_257,A_258)
      | ~ v7_waybel_0(B_257)
      | ~ v4_orders_2(B_257)
      | r1_waybel_0(A_258,B_257,C_259)
      | ~ l1_waybel_0(B_257,A_258)
      | v2_struct_0(B_257)
      | ~ l1_struct_0(A_258)
      | v2_struct_0(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_554,plain,(
    ! [B_340,A_341,A_342,B_343] :
      ( ~ v1_yellow_6(B_340,A_341)
      | ~ v7_waybel_0(B_340)
      | ~ v4_orders_2(B_340)
      | r1_waybel_0(A_341,B_340,'#skF_4'(A_342,B_343,k10_yellow_6(A_342,B_343),k4_yellow_6(A_341,B_340)))
      | ~ l1_waybel_0(B_340,A_341)
      | v2_struct_0(B_340)
      | ~ l1_struct_0(A_341)
      | v2_struct_0(A_341)
      | r2_hidden(k4_yellow_6(A_341,B_340),k10_yellow_6(A_342,B_343))
      | ~ m1_subset_1(k4_yellow_6(A_341,B_340),u1_struct_0(A_342))
      | ~ l1_waybel_0(B_343,A_342)
      | ~ v7_waybel_0(B_343)
      | ~ v4_orders_2(B_343)
      | v2_struct_0(B_343)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_262,c_247])).

tff(c_38,plain,(
    ! [A_71,B_115,D_148] :
      ( ~ r1_waybel_0(A_71,B_115,'#skF_4'(A_71,B_115,k10_yellow_6(A_71,B_115),D_148))
      | r2_hidden(D_148,k10_yellow_6(A_71,B_115))
      | ~ m1_subset_1(D_148,u1_struct_0(A_71))
      | ~ m1_subset_1(k10_yellow_6(A_71,B_115),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_waybel_0(B_115,A_71)
      | ~ v7_waybel_0(B_115)
      | ~ v4_orders_2(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_559,plain,(
    ! [A_344,B_345] :
      ( ~ m1_subset_1(k10_yellow_6(A_344,B_345),k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ v1_yellow_6(B_345,A_344)
      | ~ l1_struct_0(A_344)
      | r2_hidden(k4_yellow_6(A_344,B_345),k10_yellow_6(A_344,B_345))
      | ~ m1_subset_1(k4_yellow_6(A_344,B_345),u1_struct_0(A_344))
      | ~ l1_waybel_0(B_345,A_344)
      | ~ v7_waybel_0(B_345)
      | ~ v4_orders_2(B_345)
      | v2_struct_0(B_345)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_554,c_38])).

tff(c_563,plain,(
    ! [B_346,A_347] :
      ( ~ v1_yellow_6(B_346,A_347)
      | ~ l1_struct_0(A_347)
      | r2_hidden(k4_yellow_6(A_347,B_346),k10_yellow_6(A_347,B_346))
      | ~ m1_subset_1(k4_yellow_6(A_347,B_346),u1_struct_0(A_347))
      | ~ l1_waybel_0(B_346,A_347)
      | ~ v7_waybel_0(B_346)
      | ~ v4_orders_2(B_346)
      | v2_struct_0(B_346)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_42,c_559])).

tff(c_46,plain,(
    ~ r2_hidden(k4_yellow_6('#skF_7','#skF_8'),k10_yellow_6('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_569,plain,
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
    inference(resolution,[status(thm)],[c_563,c_46])).

tff(c_573,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_48,c_50,c_569])).

tff(c_574,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_573])).

tff(c_575,plain,(
    ~ m1_subset_1(k4_yellow_6('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_579,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ v1_yellow_6('#skF_8','#skF_7')
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_99,c_575])).

tff(c_582,plain,
    ( v2_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_579])).

tff(c_583,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_582])).

tff(c_586,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_583])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_586])).

tff(c_591,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_595,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_591])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:36:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.60  
% 3.49/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.61  %$ r1_waybel_0 > r1_orders_2 > m1_connsp_2 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_5 > #skF_4 > #skF_8 > #skF_3
% 3.49/1.61  
% 3.49/1.61  %Foreground sorts:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Background operators:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Foreground operators:
% 3.49/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.61  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.49/1.61  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.49/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.61  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.49/1.61  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.49/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.61  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 3.49/1.61  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.49/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.61  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.49/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.49/1.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.49/1.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.49/1.61  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 3.49/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.49/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.49/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.61  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.61  
% 3.86/1.63  tff(f_195, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 3.86/1.63  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.86/1.63  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.86/1.63  tff(f_173, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k4_yellow_6(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_6)).
% 3.86/1.63  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 3.86/1.63  tff(f_151, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 3.86/1.63  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 3.86/1.63  tff(f_46, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.86/1.63  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.86/1.63  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 3.86/1.63  tff(c_58, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.63  tff(c_62, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_56, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_54, plain, (v4_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_52, plain, (v7_waybel_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_50, plain, (v1_yellow_6('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_48, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.86/1.63  tff(c_72, plain, (![A_189, B_190, C_191]: (k2_waybel_0(A_189, B_190, C_191)=k4_yellow_6(A_189, B_190) | ~m1_subset_1(C_191, u1_struct_0(B_190)) | ~l1_waybel_0(B_190, A_189) | ~v1_yellow_6(B_190, A_189) | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | ~l1_struct_0(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.86/1.63  tff(c_87, plain, (![A_196, B_197]: (k2_waybel_0(A_196, B_197, '#skF_1'(u1_struct_0(B_197)))=k4_yellow_6(A_196, B_197) | ~l1_waybel_0(B_197, A_196) | ~v1_yellow_6(B_197, A_196) | ~v7_waybel_0(B_197) | ~v4_orders_2(B_197) | v2_struct_0(B_197) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(resolution, [status(thm)], [c_2, c_72])).
% 3.86/1.63  tff(c_20, plain, (![A_68, B_69, C_70]: (m1_subset_1(k2_waybel_0(A_68, B_69, C_70), u1_struct_0(A_68)) | ~m1_subset_1(C_70, u1_struct_0(B_69)) | ~l1_waybel_0(B_69, A_68) | v2_struct_0(B_69) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.86/1.63  tff(c_93, plain, (![A_196, B_197]: (m1_subset_1(k4_yellow_6(A_196, B_197), u1_struct_0(A_196)) | ~m1_subset_1('#skF_1'(u1_struct_0(B_197)), u1_struct_0(B_197)) | ~l1_waybel_0(B_197, A_196) | v2_struct_0(B_197) | ~l1_struct_0(A_196) | v2_struct_0(A_196) | ~l1_waybel_0(B_197, A_196) | ~v1_yellow_6(B_197, A_196) | ~v7_waybel_0(B_197) | ~v4_orders_2(B_197) | v2_struct_0(B_197) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(superposition, [status(thm), theory('equality')], [c_87, c_20])).
% 3.86/1.63  tff(c_99, plain, (![A_196, B_197]: (m1_subset_1(k4_yellow_6(A_196, B_197), u1_struct_0(A_196)) | ~l1_waybel_0(B_197, A_196) | ~v1_yellow_6(B_197, A_196) | ~v7_waybel_0(B_197) | ~v4_orders_2(B_197) | v2_struct_0(B_197) | ~l1_struct_0(A_196) | v2_struct_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_93])).
% 3.86/1.63  tff(c_60, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_42, plain, (![A_155, B_156]: (m1_subset_1(k10_yellow_6(A_155, B_156), k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_waybel_0(B_156, A_155) | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.86/1.63  tff(c_186, plain, (![A_231, B_232, D_233]: (m1_connsp_2('#skF_4'(A_231, B_232, k10_yellow_6(A_231, B_232), D_233), A_231, D_233) | r2_hidden(D_233, k10_yellow_6(A_231, B_232)) | ~m1_subset_1(D_233, u1_struct_0(A_231)) | ~m1_subset_1(k10_yellow_6(A_231, B_232), k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_waybel_0(B_232, A_231) | ~v7_waybel_0(B_232) | ~v4_orders_2(B_232) | v2_struct_0(B_232) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.86/1.63  tff(c_190, plain, (![A_234, B_235, D_236]: (m1_connsp_2('#skF_4'(A_234, B_235, k10_yellow_6(A_234, B_235), D_236), A_234, D_236) | r2_hidden(D_236, k10_yellow_6(A_234, B_235)) | ~m1_subset_1(D_236, u1_struct_0(A_234)) | ~l1_waybel_0(B_235, A_234) | ~v7_waybel_0(B_235) | ~v4_orders_2(B_235) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(resolution, [status(thm)], [c_42, c_186])).
% 3.86/1.63  tff(c_6, plain, (![C_7, A_4, B_5]: (m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_connsp_2(C_7, A_4, B_5) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.86/1.63  tff(c_199, plain, (![A_234, B_235, D_236]: (m1_subset_1('#skF_4'(A_234, B_235, k10_yellow_6(A_234, B_235), D_236), k1_zfmisc_1(u1_struct_0(A_234))) | r2_hidden(D_236, k10_yellow_6(A_234, B_235)) | ~m1_subset_1(D_236, u1_struct_0(A_234)) | ~l1_waybel_0(B_235, A_234) | ~v7_waybel_0(B_235) | ~v4_orders_2(B_235) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(resolution, [status(thm)], [c_190, c_6])).
% 3.86/1.63  tff(c_8, plain, (![C_14, B_12, A_8]: (r2_hidden(C_14, B_12) | ~m1_connsp_2(B_12, A_8, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_8)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.86/1.63  tff(c_258, plain, (![D_267, A_268, B_269]: (r2_hidden(D_267, '#skF_4'(A_268, B_269, k10_yellow_6(A_268, B_269), D_267)) | ~m1_subset_1('#skF_4'(A_268, B_269, k10_yellow_6(A_268, B_269), D_267), k1_zfmisc_1(u1_struct_0(A_268))) | r2_hidden(D_267, k10_yellow_6(A_268, B_269)) | ~m1_subset_1(D_267, u1_struct_0(A_268)) | ~l1_waybel_0(B_269, A_268) | ~v7_waybel_0(B_269) | ~v4_orders_2(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(resolution, [status(thm)], [c_190, c_8])).
% 3.86/1.63  tff(c_262, plain, (![D_270, A_271, B_272]: (r2_hidden(D_270, '#skF_4'(A_271, B_272, k10_yellow_6(A_271, B_272), D_270)) | r2_hidden(D_270, k10_yellow_6(A_271, B_272)) | ~m1_subset_1(D_270, u1_struct_0(A_271)) | ~l1_waybel_0(B_272, A_271) | ~v7_waybel_0(B_272) | ~v4_orders_2(B_272) | v2_struct_0(B_272) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(resolution, [status(thm)], [c_199, c_258])).
% 3.86/1.63  tff(c_18, plain, (![A_15, B_43, C_57, D_64]: (m1_subset_1('#skF_2'(A_15, B_43, C_57, D_64), u1_struct_0(B_43)) | r1_waybel_0(A_15, B_43, C_57) | ~m1_subset_1(D_64, u1_struct_0(B_43)) | ~l1_waybel_0(B_43, A_15) | v2_struct_0(B_43) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.86/1.63  tff(c_211, plain, (![C_255, B_251, A_254, A_253, D_252]: (k2_waybel_0(A_253, B_251, '#skF_2'(A_254, B_251, C_255, D_252))=k4_yellow_6(A_253, B_251) | ~l1_waybel_0(B_251, A_253) | ~v1_yellow_6(B_251, A_253) | ~v7_waybel_0(B_251) | ~v4_orders_2(B_251) | ~l1_struct_0(A_253) | v2_struct_0(A_253) | r1_waybel_0(A_254, B_251, C_255) | ~m1_subset_1(D_252, u1_struct_0(B_251)) | ~l1_waybel_0(B_251, A_254) | v2_struct_0(B_251) | ~l1_struct_0(A_254) | v2_struct_0(A_254))), inference(resolution, [status(thm)], [c_18, c_72])).
% 3.86/1.63  tff(c_231, plain, (![A_256, B_257, A_258, C_259]: (k2_waybel_0(A_256, B_257, '#skF_2'(A_258, B_257, C_259, '#skF_1'(u1_struct_0(B_257))))=k4_yellow_6(A_256, B_257) | ~l1_waybel_0(B_257, A_256) | ~v1_yellow_6(B_257, A_256) | ~v7_waybel_0(B_257) | ~v4_orders_2(B_257) | ~l1_struct_0(A_256) | v2_struct_0(A_256) | r1_waybel_0(A_258, B_257, C_259) | ~l1_waybel_0(B_257, A_258) | v2_struct_0(B_257) | ~l1_struct_0(A_258) | v2_struct_0(A_258))), inference(resolution, [status(thm)], [c_2, c_211])).
% 3.86/1.63  tff(c_14, plain, (![A_15, B_43, C_57, D_64]: (~r2_hidden(k2_waybel_0(A_15, B_43, '#skF_2'(A_15, B_43, C_57, D_64)), C_57) | r1_waybel_0(A_15, B_43, C_57) | ~m1_subset_1(D_64, u1_struct_0(B_43)) | ~l1_waybel_0(B_43, A_15) | v2_struct_0(B_43) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.86/1.63  tff(c_238, plain, (![A_258, B_257, C_259]: (~r2_hidden(k4_yellow_6(A_258, B_257), C_259) | r1_waybel_0(A_258, B_257, C_259) | ~m1_subset_1('#skF_1'(u1_struct_0(B_257)), u1_struct_0(B_257)) | ~l1_waybel_0(B_257, A_258) | v2_struct_0(B_257) | ~l1_struct_0(A_258) | v2_struct_0(A_258) | ~l1_waybel_0(B_257, A_258) | ~v1_yellow_6(B_257, A_258) | ~v7_waybel_0(B_257) | ~v4_orders_2(B_257) | ~l1_struct_0(A_258) | v2_struct_0(A_258) | r1_waybel_0(A_258, B_257, C_259) | ~l1_waybel_0(B_257, A_258) | v2_struct_0(B_257) | ~l1_struct_0(A_258) | v2_struct_0(A_258))), inference(superposition, [status(thm), theory('equality')], [c_231, c_14])).
% 3.86/1.63  tff(c_247, plain, (![A_258, B_257, C_259]: (~r2_hidden(k4_yellow_6(A_258, B_257), C_259) | ~v1_yellow_6(B_257, A_258) | ~v7_waybel_0(B_257) | ~v4_orders_2(B_257) | r1_waybel_0(A_258, B_257, C_259) | ~l1_waybel_0(B_257, A_258) | v2_struct_0(B_257) | ~l1_struct_0(A_258) | v2_struct_0(A_258))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_238])).
% 3.86/1.63  tff(c_554, plain, (![B_340, A_341, A_342, B_343]: (~v1_yellow_6(B_340, A_341) | ~v7_waybel_0(B_340) | ~v4_orders_2(B_340) | r1_waybel_0(A_341, B_340, '#skF_4'(A_342, B_343, k10_yellow_6(A_342, B_343), k4_yellow_6(A_341, B_340))) | ~l1_waybel_0(B_340, A_341) | v2_struct_0(B_340) | ~l1_struct_0(A_341) | v2_struct_0(A_341) | r2_hidden(k4_yellow_6(A_341, B_340), k10_yellow_6(A_342, B_343)) | ~m1_subset_1(k4_yellow_6(A_341, B_340), u1_struct_0(A_342)) | ~l1_waybel_0(B_343, A_342) | ~v7_waybel_0(B_343) | ~v4_orders_2(B_343) | v2_struct_0(B_343) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(resolution, [status(thm)], [c_262, c_247])).
% 3.86/1.63  tff(c_38, plain, (![A_71, B_115, D_148]: (~r1_waybel_0(A_71, B_115, '#skF_4'(A_71, B_115, k10_yellow_6(A_71, B_115), D_148)) | r2_hidden(D_148, k10_yellow_6(A_71, B_115)) | ~m1_subset_1(D_148, u1_struct_0(A_71)) | ~m1_subset_1(k10_yellow_6(A_71, B_115), k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_waybel_0(B_115, A_71) | ~v7_waybel_0(B_115) | ~v4_orders_2(B_115) | v2_struct_0(B_115) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.86/1.63  tff(c_559, plain, (![A_344, B_345]: (~m1_subset_1(k10_yellow_6(A_344, B_345), k1_zfmisc_1(u1_struct_0(A_344))) | ~v1_yellow_6(B_345, A_344) | ~l1_struct_0(A_344) | r2_hidden(k4_yellow_6(A_344, B_345), k10_yellow_6(A_344, B_345)) | ~m1_subset_1(k4_yellow_6(A_344, B_345), u1_struct_0(A_344)) | ~l1_waybel_0(B_345, A_344) | ~v7_waybel_0(B_345) | ~v4_orders_2(B_345) | v2_struct_0(B_345) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(resolution, [status(thm)], [c_554, c_38])).
% 3.86/1.63  tff(c_563, plain, (![B_346, A_347]: (~v1_yellow_6(B_346, A_347) | ~l1_struct_0(A_347) | r2_hidden(k4_yellow_6(A_347, B_346), k10_yellow_6(A_347, B_346)) | ~m1_subset_1(k4_yellow_6(A_347, B_346), u1_struct_0(A_347)) | ~l1_waybel_0(B_346, A_347) | ~v7_waybel_0(B_346) | ~v4_orders_2(B_346) | v2_struct_0(B_346) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(resolution, [status(thm)], [c_42, c_559])).
% 3.86/1.63  tff(c_46, plain, (~r2_hidden(k4_yellow_6('#skF_7', '#skF_8'), k10_yellow_6('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.86/1.63  tff(c_569, plain, (~v1_yellow_6('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7') | ~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_563, c_46])).
% 3.86/1.63  tff(c_573, plain, (~l1_struct_0('#skF_7') | ~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_48, c_50, c_569])).
% 3.86/1.63  tff(c_574, plain, (~l1_struct_0('#skF_7') | ~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_573])).
% 3.86/1.63  tff(c_575, plain, (~m1_subset_1(k4_yellow_6('#skF_7', '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_574])).
% 3.86/1.63  tff(c_579, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~v1_yellow_6('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_99, c_575])).
% 3.86/1.63  tff(c_582, plain, (v2_struct_0('#skF_8') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_579])).
% 3.86/1.63  tff(c_583, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_582])).
% 3.86/1.63  tff(c_586, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_4, c_583])).
% 3.86/1.63  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_586])).
% 3.86/1.63  tff(c_591, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_574])).
% 3.86/1.63  tff(c_595, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_4, c_591])).
% 3.86/1.63  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_595])).
% 3.86/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.63  
% 3.86/1.63  Inference rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Ref     : 0
% 3.86/1.63  #Sup     : 135
% 3.86/1.63  #Fact    : 0
% 3.86/1.63  #Define  : 0
% 3.86/1.63  #Split   : 1
% 3.86/1.63  #Chain   : 0
% 3.86/1.63  #Close   : 0
% 3.86/1.63  
% 3.86/1.63  Ordering : KBO
% 3.86/1.63  
% 3.86/1.63  Simplification rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Subsume      : 43
% 3.86/1.63  #Demod        : 18
% 3.86/1.63  #Tautology    : 32
% 3.86/1.63  #SimpNegUnit  : 2
% 3.86/1.63  #BackRed      : 0
% 3.86/1.63  
% 3.86/1.63  #Partial instantiations: 0
% 3.86/1.63  #Strategies tried      : 1
% 3.86/1.63  
% 3.86/1.63  Timing (in seconds)
% 3.86/1.63  ----------------------
% 3.86/1.63  Preprocessing        : 0.38
% 3.86/1.63  Parsing              : 0.19
% 3.86/1.63  CNF conversion       : 0.04
% 3.86/1.63  Main loop            : 0.48
% 3.86/1.63  Inferencing          : 0.21
% 3.86/1.63  Reduction            : 0.11
% 3.86/1.63  Demodulation         : 0.08
% 3.86/1.63  BG Simplification    : 0.03
% 3.86/1.63  Subsumption          : 0.10
% 3.86/1.63  Abstraction          : 0.03
% 3.86/1.63  MUC search           : 0.00
% 3.86/1.63  Cooper               : 0.00
% 3.86/1.63  Total                : 0.90
% 3.86/1.63  Index Insertion      : 0.00
% 3.86/1.63  Index Deletion       : 0.00
% 3.86/1.63  Index Matching       : 0.00
% 3.86/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
