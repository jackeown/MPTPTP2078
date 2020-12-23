%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1660+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:12 EST 2020

% Result     : Theorem 11.00s
% Output     : CNFRefutation 11.00s
% Verified   : 
% Statistics : Number of formulae       :  151 (1446 expanded)
%              Number of leaves         :   29 ( 523 expanded)
%              Depth                    :   23
%              Number of atoms          :  627 (9316 expanded)
%              Number of equality atoms :   23 ( 289 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v1_waybel_0 > v12_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( v12_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_waybel_0(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( ( r2_hidden(C,B)
                          & r2_hidden(D,B) )
                       => r2_hidden(k13_lattice3(A,C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_waybel_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(C,B)
                        & r2_hidden(D,B)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,B)
                                & r1_orders_2(A,C,E)
                                & r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v12_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,D,C) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

tff(c_56,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v1_lattice3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,
    ( r2_hidden('#skF_10','#skF_8')
    | ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_81,plain,(
    ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_26,B_56] :
      ( m1_subset_1('#skF_4'(A_26,B_56),u1_struct_0(A_26))
      | v1_waybel_0(B_56,A_26)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_26,B_56] :
      ( m1_subset_1('#skF_5'(A_26,B_56),u1_struct_0(A_26))
      | v1_waybel_0(B_56,A_26)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_82,B_83,C_84] :
      ( m1_subset_1(k13_lattice3(A_82,B_83,C_84),u1_struct_0(A_82))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_113,plain,(
    ! [A_177,B_178,C_179] :
      ( r1_orders_2(A_177,B_178,k13_lattice3(A_177,B_178,C_179))
      | ~ m1_subset_1(k13_lattice3(A_177,B_178,C_179),u1_struct_0(A_177))
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ l1_orders_2(A_177)
      | ~ v1_lattice3(A_177)
      | ~ v5_orders_2(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_116,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_orders_2(A_82,B_83,k13_lattice3(A_82,B_83,C_84))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_118,plain,(
    ! [A_183,C_184,B_185] :
      ( r1_orders_2(A_183,C_184,k13_lattice3(A_183,B_185,C_184))
      | ~ m1_subset_1(k13_lattice3(A_183,B_185,C_184),u1_struct_0(A_183))
      | ~ m1_subset_1(C_184,u1_struct_0(A_183))
      | ~ m1_subset_1(B_185,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183)
      | ~ v1_lattice3(A_183)
      | ~ v5_orders_2(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_121,plain,(
    ! [A_82,C_84,B_83] :
      ( r1_orders_2(A_82,C_84,k13_lattice3(A_82,B_83,C_84))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_118])).

tff(c_218,plain,(
    ! [A_242,B_243,C_244,E_245] :
      ( r1_orders_2(A_242,k13_lattice3(A_242,B_243,C_244),E_245)
      | ~ r1_orders_2(A_242,C_244,E_245)
      | ~ r1_orders_2(A_242,B_243,E_245)
      | ~ m1_subset_1(E_245,u1_struct_0(A_242))
      | ~ m1_subset_1(k13_lattice3(A_242,B_243,C_244),u1_struct_0(A_242))
      | ~ m1_subset_1(C_244,u1_struct_0(A_242))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l1_orders_2(A_242)
      | ~ v1_lattice3(A_242)
      | ~ v5_orders_2(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_221,plain,(
    ! [A_82,B_83,C_84,E_245] :
      ( r1_orders_2(A_82,k13_lattice3(A_82,B_83,C_84),E_245)
      | ~ r1_orders_2(A_82,C_84,E_245)
      | ~ r1_orders_2(A_82,B_83,E_245)
      | ~ m1_subset_1(E_245,u1_struct_0(A_82))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_218])).

tff(c_174,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( r1_orders_2(A_224,B_225,'#skF_6'(A_224,B_225,C_226,D_227))
      | k13_lattice3(A_224,B_225,C_226) = D_227
      | ~ r1_orders_2(A_224,C_226,D_227)
      | ~ r1_orders_2(A_224,B_225,D_227)
      | ~ m1_subset_1(D_227,u1_struct_0(A_224))
      | ~ m1_subset_1(C_226,u1_struct_0(A_224))
      | ~ m1_subset_1(B_225,u1_struct_0(A_224))
      | ~ l1_orders_2(A_224)
      | ~ v1_lattice3(A_224)
      | ~ v5_orders_2(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    ! [A_85,D_127,B_109,C_121] :
      ( ~ r1_orders_2(A_85,D_127,'#skF_6'(A_85,B_109,C_121,D_127))
      | k13_lattice3(A_85,B_109,C_121) = D_127
      | ~ r1_orders_2(A_85,C_121,D_127)
      | ~ r1_orders_2(A_85,B_109,D_127)
      | ~ m1_subset_1(D_127,u1_struct_0(A_85))
      | ~ m1_subset_1(C_121,u1_struct_0(A_85))
      | ~ m1_subset_1(B_109,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85)
      | ~ v1_lattice3(A_85)
      | ~ v5_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_188,plain,(
    ! [A_232,D_233,C_234] :
      ( k13_lattice3(A_232,D_233,C_234) = D_233
      | ~ r1_orders_2(A_232,C_234,D_233)
      | ~ r1_orders_2(A_232,D_233,D_233)
      | ~ m1_subset_1(C_234,u1_struct_0(A_232))
      | ~ m1_subset_1(D_233,u1_struct_0(A_232))
      | ~ l1_orders_2(A_232)
      | ~ v1_lattice3(A_232)
      | ~ v5_orders_2(A_232) ) ),
    inference(resolution,[status(thm)],[c_174,c_34])).

tff(c_265,plain,(
    ! [A_268,B_269,C_270] :
      ( k13_lattice3(A_268,k13_lattice3(A_268,B_269,C_270),B_269) = k13_lattice3(A_268,B_269,C_270)
      | ~ r1_orders_2(A_268,k13_lattice3(A_268,B_269,C_270),k13_lattice3(A_268,B_269,C_270))
      | ~ m1_subset_1(k13_lattice3(A_268,B_269,C_270),u1_struct_0(A_268))
      | ~ m1_subset_1(C_270,u1_struct_0(A_268))
      | ~ m1_subset_1(B_269,u1_struct_0(A_268))
      | ~ l1_orders_2(A_268)
      | ~ v1_lattice3(A_268)
      | ~ v5_orders_2(A_268) ) ),
    inference(resolution,[status(thm)],[c_116,c_188])).

tff(c_1186,plain,(
    ! [A_357,B_358,C_359] :
      ( k13_lattice3(A_357,k13_lattice3(A_357,B_358,C_359),B_358) = k13_lattice3(A_357,B_358,C_359)
      | ~ r1_orders_2(A_357,C_359,k13_lattice3(A_357,B_358,C_359))
      | ~ r1_orders_2(A_357,B_358,k13_lattice3(A_357,B_358,C_359))
      | ~ m1_subset_1(k13_lattice3(A_357,B_358,C_359),u1_struct_0(A_357))
      | ~ m1_subset_1(C_359,u1_struct_0(A_357))
      | ~ m1_subset_1(B_358,u1_struct_0(A_357))
      | ~ l1_orders_2(A_357)
      | ~ v1_lattice3(A_357)
      | ~ v5_orders_2(A_357) ) ),
    inference(resolution,[status(thm)],[c_221,c_265])).

tff(c_1218,plain,(
    ! [A_360,B_361,C_362] :
      ( k13_lattice3(A_360,k13_lattice3(A_360,B_361,C_362),B_361) = k13_lattice3(A_360,B_361,C_362)
      | ~ r1_orders_2(A_360,B_361,k13_lattice3(A_360,B_361,C_362))
      | ~ m1_subset_1(k13_lattice3(A_360,B_361,C_362),u1_struct_0(A_360))
      | ~ m1_subset_1(C_362,u1_struct_0(A_360))
      | ~ m1_subset_1(B_361,u1_struct_0(A_360))
      | ~ l1_orders_2(A_360)
      | ~ v1_lattice3(A_360)
      | ~ v5_orders_2(A_360) ) ),
    inference(resolution,[status(thm)],[c_121,c_1186])).

tff(c_1250,plain,(
    ! [A_363,B_364,C_365] :
      ( k13_lattice3(A_363,k13_lattice3(A_363,B_364,C_365),B_364) = k13_lattice3(A_363,B_364,C_365)
      | ~ m1_subset_1(k13_lattice3(A_363,B_364,C_365),u1_struct_0(A_363))
      | ~ m1_subset_1(C_365,u1_struct_0(A_363))
      | ~ m1_subset_1(B_364,u1_struct_0(A_363))
      | ~ l1_orders_2(A_363)
      | ~ v1_lattice3(A_363)
      | ~ v5_orders_2(A_363) ) ),
    inference(resolution,[status(thm)],[c_116,c_1218])).

tff(c_1274,plain,(
    ! [A_366,B_367,C_368] :
      ( k13_lattice3(A_366,k13_lattice3(A_366,B_367,C_368),B_367) = k13_lattice3(A_366,B_367,C_368)
      | ~ m1_subset_1(C_368,u1_struct_0(A_366))
      | ~ m1_subset_1(B_367,u1_struct_0(A_366))
      | ~ l1_orders_2(A_366)
      | ~ v1_lattice3(A_366)
      | ~ v5_orders_2(A_366) ) ),
    inference(resolution,[status(thm)],[c_32,c_1250])).

tff(c_1308,plain,(
    ! [A_372,B_373,B_374] :
      ( k13_lattice3(A_372,k13_lattice3(A_372,B_373,'#skF_5'(A_372,B_374)),B_373) = k13_lattice3(A_372,B_373,'#skF_5'(A_372,B_374))
      | ~ m1_subset_1(B_373,u1_struct_0(A_372))
      | ~ v1_lattice3(A_372)
      | ~ v5_orders_2(A_372)
      | v1_waybel_0(B_374,A_372)
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_orders_2(A_372) ) ),
    inference(resolution,[status(thm)],[c_20,c_1274])).

tff(c_1310,plain,(
    ! [B_373] :
      ( k13_lattice3('#skF_7',k13_lattice3('#skF_7',B_373,'#skF_5'('#skF_7','#skF_8')),B_373) = k13_lattice3('#skF_7',B_373,'#skF_5'('#skF_7','#skF_8'))
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_7'))
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | v1_waybel_0('#skF_8','#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_1308])).

tff(c_1313,plain,(
    ! [B_373] :
      ( k13_lattice3('#skF_7',k13_lattice3('#skF_7',B_373,'#skF_5'('#skF_7','#skF_8')),B_373) = k13_lattice3('#skF_7',B_373,'#skF_5'('#skF_7','#skF_8'))
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_7'))
      | v1_waybel_0('#skF_8','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_1310])).

tff(c_1315,plain,(
    ! [B_375] :
      ( k13_lattice3('#skF_7',k13_lattice3('#skF_7',B_375,'#skF_5'('#skF_7','#skF_8')),B_375) = k13_lattice3('#skF_7',B_375,'#skF_5'('#skF_7','#skF_8'))
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1313])).

tff(c_1381,plain,(
    ! [B_375] :
      ( r1_orders_2('#skF_7',B_375,k13_lattice3('#skF_7',B_375,'#skF_5'('#skF_7','#skF_8')))
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(k13_lattice3('#skF_7',B_375,'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_121])).

tff(c_1479,plain,(
    ! [B_376] :
      ( r1_orders_2('#skF_7',B_376,k13_lattice3('#skF_7',B_376,'#skF_5'('#skF_7','#skF_8')))
      | ~ m1_subset_1(k13_lattice3('#skF_7',B_376,'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_376,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1381])).

tff(c_1491,plain,(
    ! [B_83] :
      ( r1_orders_2('#skF_7',B_83,k13_lattice3('#skF_7',B_83,'#skF_5'('#skF_7','#skF_8')))
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_1479])).

tff(c_1500,plain,(
    ! [B_83] :
      ( r1_orders_2('#skF_7',B_83,k13_lattice3('#skF_7',B_83,'#skF_5'('#skF_7','#skF_8')))
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1491])).

tff(c_1566,plain,(
    ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1500])).

tff(c_1569,plain,
    ( v1_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_1566])).

tff(c_1572,plain,(
    v1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1569])).

tff(c_1574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1572])).

tff(c_1576,plain,(
    m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1500])).

tff(c_1592,plain,(
    ! [B_378] :
      ( r1_orders_2('#skF_7',B_378,k13_lattice3('#skF_7',B_378,'#skF_5'('#skF_7','#skF_8')))
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_1500])).

tff(c_133,plain,(
    ! [A_193,B_194,E_195] :
      ( ~ r1_orders_2(A_193,'#skF_5'(A_193,B_194),E_195)
      | ~ r1_orders_2(A_193,'#skF_4'(A_193,B_194),E_195)
      | ~ r2_hidden(E_195,B_194)
      | ~ m1_subset_1(E_195,u1_struct_0(A_193))
      | v1_waybel_0(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_orders_2(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_140,plain,(
    ! [A_82,B_194,B_83] :
      ( ~ r1_orders_2(A_82,'#skF_4'(A_82,B_194),k13_lattice3(A_82,B_83,'#skF_5'(A_82,B_194)))
      | ~ r2_hidden(k13_lattice3(A_82,B_83,'#skF_5'(A_82,B_194)),B_194)
      | ~ m1_subset_1(k13_lattice3(A_82,B_83,'#skF_5'(A_82,B_194)),u1_struct_0(A_82))
      | v1_waybel_0(B_194,A_82)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1('#skF_5'(A_82,B_194),u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_121,c_133])).

tff(c_1596,plain,
    ( ~ r2_hidden(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),'#skF_8')
    | ~ m1_subset_1(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7'))
    | v1_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1592,c_140])).

tff(c_1618,plain,
    ( ~ r2_hidden(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),'#skF_8')
    | ~ m1_subset_1(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7'))
    | v1_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1576,c_48,c_1596])).

tff(c_1619,plain,
    ( ~ r2_hidden(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),'#skF_8')
    | ~ m1_subset_1(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1618])).

tff(c_2411,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1619])).

tff(c_2414,plain,
    ( v1_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_2411])).

tff(c_2417,plain,(
    v1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_2414])).

tff(c_2419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2417])).

tff(c_2421,plain,(
    m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1619])).

tff(c_96,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_4'(A_160,B_161),B_161)
      | v1_waybel_0(B_161,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_orders_2(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | v1_waybel_0('#skF_8','#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_101,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | v1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_98])).

tff(c_102,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_101])).

tff(c_83,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_5'(A_156,B_157),B_157)
      | v1_waybel_0(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_orders_2(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_8'),'#skF_8')
    | v1_waybel_0('#skF_8','#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_83])).

tff(c_88,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_8'),'#skF_8')
    | v1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_89,plain,(
    r2_hidden('#skF_5'('#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_88])).

tff(c_80,plain,(
    ! [C_151,D_153] :
      ( v1_waybel_0('#skF_8','#skF_7')
      | r2_hidden(k13_lattice3('#skF_7',C_151,D_153),'#skF_8')
      | ~ r2_hidden(D_153,'#skF_8')
      | ~ r2_hidden(C_151,'#skF_8')
      | ~ m1_subset_1(D_153,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_111,plain,(
    ! [C_151,D_153] :
      ( r2_hidden(k13_lattice3('#skF_7',C_151,D_153),'#skF_8')
      | ~ r2_hidden(D_153,'#skF_8')
      | ~ r2_hidden(C_151,'#skF_8')
      | ~ m1_subset_1(D_153,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_80])).

tff(c_2420,plain,
    ( ~ m1_subset_1(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7'))
    | ~ r2_hidden(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1619])).

tff(c_2652,plain,(
    ~ r2_hidden(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2420])).

tff(c_2656,plain,
    ( ~ r2_hidden('#skF_5'('#skF_7','#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_111,c_2652])).

tff(c_2660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_1576,c_102,c_89,c_2656])).

tff(c_2661,plain,(
    ~ m1_subset_1(k13_lattice3('#skF_7','#skF_4'('#skF_7','#skF_8'),'#skF_5'('#skF_7','#skF_8')),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2420])).

tff(c_2678,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_2661])).

tff(c_2682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2421,c_1576,c_2678])).

tff(c_2684,plain,(
    v1_waybel_0('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( m1_subset_1('#skF_10',u1_struct_0('#skF_7'))
    | ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2694,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2684,c_64])).

tff(c_66,plain,
    ( m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2692,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2684,c_66])).

tff(c_2683,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2685,plain,(
    ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2684,c_2685])).

tff(c_2688,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2764,plain,(
    ! [A_449,D_450,B_451,C_452] :
      ( r1_orders_2(A_449,D_450,'#skF_3'(A_449,B_451,C_452,D_450))
      | ~ r2_hidden(D_450,B_451)
      | ~ r2_hidden(C_452,B_451)
      | ~ m1_subset_1(D_450,u1_struct_0(A_449))
      | ~ m1_subset_1(C_452,u1_struct_0(A_449))
      | ~ v1_waybel_0(B_451,A_449)
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0(A_449)))
      | ~ l1_orders_2(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2766,plain,(
    ! [D_450,C_452] :
      ( r1_orders_2('#skF_7',D_450,'#skF_3'('#skF_7','#skF_8',C_452,D_450))
      | ~ r2_hidden(D_450,'#skF_8')
      | ~ r2_hidden(C_452,'#skF_8')
      | ~ m1_subset_1(D_450,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_452,u1_struct_0('#skF_7'))
      | ~ v1_waybel_0('#skF_8','#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_2764])).

tff(c_2769,plain,(
    ! [D_450,C_452] :
      ( r1_orders_2('#skF_7',D_450,'#skF_3'('#skF_7','#skF_8',C_452,D_450))
      | ~ r2_hidden(D_450,'#skF_8')
      | ~ r2_hidden(C_452,'#skF_8')
      | ~ m1_subset_1(D_450,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_452,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2684,c_2766])).

tff(c_2782,plain,(
    ! [A_455,C_456,B_457,D_458] :
      ( r1_orders_2(A_455,C_456,'#skF_3'(A_455,B_457,C_456,D_458))
      | ~ r2_hidden(D_458,B_457)
      | ~ r2_hidden(C_456,B_457)
      | ~ m1_subset_1(D_458,u1_struct_0(A_455))
      | ~ m1_subset_1(C_456,u1_struct_0(A_455))
      | ~ v1_waybel_0(B_457,A_455)
      | ~ m1_subset_1(B_457,k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ l1_orders_2(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2784,plain,(
    ! [C_456,D_458] :
      ( r1_orders_2('#skF_7',C_456,'#skF_3'('#skF_7','#skF_8',C_456,D_458))
      | ~ r2_hidden(D_458,'#skF_8')
      | ~ r2_hidden(C_456,'#skF_8')
      | ~ m1_subset_1(D_458,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_456,u1_struct_0('#skF_7'))
      | ~ v1_waybel_0('#skF_8','#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_2782])).

tff(c_2787,plain,(
    ! [C_456,D_458] :
      ( r1_orders_2('#skF_7',C_456,'#skF_3'('#skF_7','#skF_8',C_456,D_458))
      | ~ r2_hidden(D_458,'#skF_8')
      | ~ r2_hidden(C_456,'#skF_8')
      | ~ m1_subset_1(D_458,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_456,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2684,c_2784])).

tff(c_30,plain,(
    ! [A_26,B_56,C_71,D_75] :
      ( m1_subset_1('#skF_3'(A_26,B_56,C_71,D_75),u1_struct_0(A_26))
      | ~ r2_hidden(D_75,B_56)
      | ~ r2_hidden(C_71,B_56)
      | ~ m1_subset_1(D_75,u1_struct_0(A_26))
      | ~ m1_subset_1(C_71,u1_struct_0(A_26))
      | ~ v1_waybel_0(B_56,A_26)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,
    ( ~ r2_hidden(k13_lattice3('#skF_7','#skF_9','#skF_10'),'#skF_8')
    | ~ v1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2696,plain,(
    ~ r2_hidden(k13_lattice3('#skF_7','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2684,c_58])).

tff(c_50,plain,(
    v12_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2732,plain,(
    ! [A_426,B_427,C_428] :
      ( r1_orders_2(A_426,B_427,k13_lattice3(A_426,B_427,C_428))
      | ~ m1_subset_1(k13_lattice3(A_426,B_427,C_428),u1_struct_0(A_426))
      | ~ m1_subset_1(C_428,u1_struct_0(A_426))
      | ~ m1_subset_1(B_427,u1_struct_0(A_426))
      | ~ l1_orders_2(A_426)
      | ~ v1_lattice3(A_426)
      | ~ v5_orders_2(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2735,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_orders_2(A_82,B_83,k13_lattice3(A_82,B_83,C_84))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_2732])).

tff(c_2727,plain,(
    ! [A_420,C_421,B_422] :
      ( r1_orders_2(A_420,C_421,k13_lattice3(A_420,B_422,C_421))
      | ~ m1_subset_1(k13_lattice3(A_420,B_422,C_421),u1_struct_0(A_420))
      | ~ m1_subset_1(C_421,u1_struct_0(A_420))
      | ~ m1_subset_1(B_422,u1_struct_0(A_420))
      | ~ l1_orders_2(A_420)
      | ~ v1_lattice3(A_420)
      | ~ v5_orders_2(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2730,plain,(
    ! [A_82,C_84,B_83] :
      ( r1_orders_2(A_82,C_84,k13_lattice3(A_82,B_83,C_84))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_2727])).

tff(c_2863,plain,(
    ! [A_494,B_495,C_496,E_497] :
      ( r1_orders_2(A_494,k13_lattice3(A_494,B_495,C_496),E_497)
      | ~ r1_orders_2(A_494,C_496,E_497)
      | ~ r1_orders_2(A_494,B_495,E_497)
      | ~ m1_subset_1(E_497,u1_struct_0(A_494))
      | ~ m1_subset_1(k13_lattice3(A_494,B_495,C_496),u1_struct_0(A_494))
      | ~ m1_subset_1(C_496,u1_struct_0(A_494))
      | ~ m1_subset_1(B_495,u1_struct_0(A_494))
      | ~ l1_orders_2(A_494)
      | ~ v1_lattice3(A_494)
      | ~ v5_orders_2(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2866,plain,(
    ! [A_82,B_83,C_84,E_497] :
      ( r1_orders_2(A_82,k13_lattice3(A_82,B_83,C_84),E_497)
      | ~ r1_orders_2(A_82,C_84,E_497)
      | ~ r1_orders_2(A_82,B_83,E_497)
      | ~ m1_subset_1(E_497,u1_struct_0(A_82))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_32,c_2863])).

tff(c_2809,plain,(
    ! [A_476,B_477,C_478,D_479] :
      ( r1_orders_2(A_476,B_477,'#skF_6'(A_476,B_477,C_478,D_479))
      | k13_lattice3(A_476,B_477,C_478) = D_479
      | ~ r1_orders_2(A_476,C_478,D_479)
      | ~ r1_orders_2(A_476,B_477,D_479)
      | ~ m1_subset_1(D_479,u1_struct_0(A_476))
      | ~ m1_subset_1(C_478,u1_struct_0(A_476))
      | ~ m1_subset_1(B_477,u1_struct_0(A_476))
      | ~ l1_orders_2(A_476)
      | ~ v1_lattice3(A_476)
      | ~ v5_orders_2(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2822,plain,(
    ! [A_480,D_481,C_482] :
      ( k13_lattice3(A_480,D_481,C_482) = D_481
      | ~ r1_orders_2(A_480,C_482,D_481)
      | ~ r1_orders_2(A_480,D_481,D_481)
      | ~ m1_subset_1(C_482,u1_struct_0(A_480))
      | ~ m1_subset_1(D_481,u1_struct_0(A_480))
      | ~ l1_orders_2(A_480)
      | ~ v1_lattice3(A_480)
      | ~ v5_orders_2(A_480) ) ),
    inference(resolution,[status(thm)],[c_2809,c_34])).

tff(c_2910,plain,(
    ! [A_520,B_521,C_522] :
      ( k13_lattice3(A_520,k13_lattice3(A_520,B_521,C_522),B_521) = k13_lattice3(A_520,B_521,C_522)
      | ~ r1_orders_2(A_520,k13_lattice3(A_520,B_521,C_522),k13_lattice3(A_520,B_521,C_522))
      | ~ m1_subset_1(k13_lattice3(A_520,B_521,C_522),u1_struct_0(A_520))
      | ~ m1_subset_1(C_522,u1_struct_0(A_520))
      | ~ m1_subset_1(B_521,u1_struct_0(A_520))
      | ~ l1_orders_2(A_520)
      | ~ v1_lattice3(A_520)
      | ~ v5_orders_2(A_520) ) ),
    inference(resolution,[status(thm)],[c_2735,c_2822])).

tff(c_2929,plain,(
    ! [A_534,B_535,C_536] :
      ( k13_lattice3(A_534,k13_lattice3(A_534,B_535,C_536),B_535) = k13_lattice3(A_534,B_535,C_536)
      | ~ r1_orders_2(A_534,C_536,k13_lattice3(A_534,B_535,C_536))
      | ~ r1_orders_2(A_534,B_535,k13_lattice3(A_534,B_535,C_536))
      | ~ m1_subset_1(k13_lattice3(A_534,B_535,C_536),u1_struct_0(A_534))
      | ~ m1_subset_1(C_536,u1_struct_0(A_534))
      | ~ m1_subset_1(B_535,u1_struct_0(A_534))
      | ~ l1_orders_2(A_534)
      | ~ v1_lattice3(A_534)
      | ~ v5_orders_2(A_534) ) ),
    inference(resolution,[status(thm)],[c_2866,c_2910])).

tff(c_4500,plain,(
    ! [A_653,B_654,C_655] :
      ( k13_lattice3(A_653,k13_lattice3(A_653,B_654,C_655),B_654) = k13_lattice3(A_653,B_654,C_655)
      | ~ r1_orders_2(A_653,B_654,k13_lattice3(A_653,B_654,C_655))
      | ~ m1_subset_1(k13_lattice3(A_653,B_654,C_655),u1_struct_0(A_653))
      | ~ m1_subset_1(C_655,u1_struct_0(A_653))
      | ~ m1_subset_1(B_654,u1_struct_0(A_653))
      | ~ l1_orders_2(A_653)
      | ~ v1_lattice3(A_653)
      | ~ v5_orders_2(A_653) ) ),
    inference(resolution,[status(thm)],[c_2730,c_2929])).

tff(c_4554,plain,(
    ! [A_656,B_657,C_658] :
      ( k13_lattice3(A_656,k13_lattice3(A_656,B_657,C_658),B_657) = k13_lattice3(A_656,B_657,C_658)
      | ~ m1_subset_1(k13_lattice3(A_656,B_657,C_658),u1_struct_0(A_656))
      | ~ m1_subset_1(C_658,u1_struct_0(A_656))
      | ~ m1_subset_1(B_657,u1_struct_0(A_656))
      | ~ l1_orders_2(A_656)
      | ~ v1_lattice3(A_656)
      | ~ v5_orders_2(A_656) ) ),
    inference(resolution,[status(thm)],[c_2735,c_4500])).

tff(c_4600,plain,(
    ! [A_659,B_660,C_661] :
      ( k13_lattice3(A_659,k13_lattice3(A_659,B_660,C_661),B_660) = k13_lattice3(A_659,B_660,C_661)
      | ~ m1_subset_1(C_661,u1_struct_0(A_659))
      | ~ m1_subset_1(B_660,u1_struct_0(A_659))
      | ~ l1_orders_2(A_659)
      | ~ v1_lattice3(A_659)
      | ~ v5_orders_2(A_659) ) ),
    inference(resolution,[status(thm)],[c_32,c_4554])).

tff(c_4620,plain,(
    ! [B_660] :
      ( k13_lattice3('#skF_7',k13_lattice3('#skF_7',B_660,'#skF_10'),B_660) = k13_lattice3('#skF_7',B_660,'#skF_10')
      | ~ m1_subset_1(B_660,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2694,c_4600])).

tff(c_4642,plain,(
    ! [B_662] :
      ( k13_lattice3('#skF_7',k13_lattice3('#skF_7',B_662,'#skF_10'),B_662) = k13_lattice3('#skF_7',B_662,'#skF_10')
      | ~ m1_subset_1(B_662,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_4620])).

tff(c_4698,plain,(
    k13_lattice3('#skF_7',k13_lattice3('#skF_7','#skF_9','#skF_10'),'#skF_9') = k13_lattice3('#skF_7','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_2692,c_4642])).

tff(c_4726,plain,
    ( r1_orders_2('#skF_7','#skF_9',k13_lattice3('#skF_7','#skF_9','#skF_10'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_7','#skF_9','#skF_10'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4698,c_2730])).

tff(c_4751,plain,
    ( r1_orders_2('#skF_7','#skF_9',k13_lattice3('#skF_7','#skF_9','#skF_10'))
    | ~ m1_subset_1(k13_lattice3('#skF_7','#skF_9','#skF_10'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2692,c_4726])).

tff(c_4755,plain,(
    ~ m1_subset_1(k13_lattice3('#skF_7','#skF_9','#skF_10'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4751])).

tff(c_4758,plain,
    ( ~ m1_subset_1('#skF_10',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7')
    | ~ v1_lattice3('#skF_7')
    | ~ v5_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_4755])).

tff(c_4762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2692,c_2694,c_4758])).

tff(c_4764,plain,(
    m1_subset_1(k13_lattice3('#skF_7','#skF_9','#skF_10'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4751])).

tff(c_2756,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( r2_hidden('#skF_3'(A_439,B_440,C_441,D_442),B_440)
      | ~ r2_hidden(D_442,B_440)
      | ~ r2_hidden(C_441,B_440)
      | ~ m1_subset_1(D_442,u1_struct_0(A_439))
      | ~ m1_subset_1(C_441,u1_struct_0(A_439))
      | ~ v1_waybel_0(B_440,A_439)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ l1_orders_2(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2758,plain,(
    ! [C_441,D_442] :
      ( r2_hidden('#skF_3'('#skF_7','#skF_8',C_441,D_442),'#skF_8')
      | ~ r2_hidden(D_442,'#skF_8')
      | ~ r2_hidden(C_441,'#skF_8')
      | ~ m1_subset_1(D_442,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_441,u1_struct_0('#skF_7'))
      | ~ v1_waybel_0('#skF_8','#skF_7')
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_2756])).

tff(c_2761,plain,(
    ! [C_441,D_442] :
      ( r2_hidden('#skF_3'('#skF_7','#skF_8',C_441,D_442),'#skF_8')
      | ~ r2_hidden(D_442,'#skF_8')
      | ~ r2_hidden(C_441,'#skF_8')
      | ~ m1_subset_1(D_442,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_441,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2684,c_2758])).

tff(c_2873,plain,(
    ! [A_501,B_502,C_503,E_504] :
      ( r1_orders_2(A_501,k13_lattice3(A_501,B_502,C_503),E_504)
      | ~ r1_orders_2(A_501,C_503,E_504)
      | ~ r1_orders_2(A_501,B_502,E_504)
      | ~ m1_subset_1(E_504,u1_struct_0(A_501))
      | ~ m1_subset_1(C_503,u1_struct_0(A_501))
      | ~ m1_subset_1(B_502,u1_struct_0(A_501))
      | ~ l1_orders_2(A_501)
      | ~ v1_lattice3(A_501)
      | ~ v5_orders_2(A_501) ) ),
    inference(resolution,[status(thm)],[c_32,c_2863])).

tff(c_2,plain,(
    ! [D_24,B_15,A_1,C_22] :
      ( r2_hidden(D_24,B_15)
      | ~ r1_orders_2(A_1,D_24,C_22)
      | ~ r2_hidden(C_22,B_15)
      | ~ m1_subset_1(D_24,u1_struct_0(A_1))
      | ~ m1_subset_1(C_22,u1_struct_0(A_1))
      | ~ v12_waybel_0(B_15,A_1)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3562,plain,(
    ! [A_566,B_569,E_570,C_568,B_567] :
      ( r2_hidden(k13_lattice3(A_566,B_567,C_568),B_569)
      | ~ r2_hidden(E_570,B_569)
      | ~ m1_subset_1(k13_lattice3(A_566,B_567,C_568),u1_struct_0(A_566))
      | ~ v12_waybel_0(B_569,A_566)
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ r1_orders_2(A_566,C_568,E_570)
      | ~ r1_orders_2(A_566,B_567,E_570)
      | ~ m1_subset_1(E_570,u1_struct_0(A_566))
      | ~ m1_subset_1(C_568,u1_struct_0(A_566))
      | ~ m1_subset_1(B_567,u1_struct_0(A_566))
      | ~ l1_orders_2(A_566)
      | ~ v1_lattice3(A_566)
      | ~ v5_orders_2(A_566) ) ),
    inference(resolution,[status(thm)],[c_2873,c_2])).

tff(c_5598,plain,(
    ! [C_678,A_676,D_677,C_675,B_679] :
      ( r2_hidden(k13_lattice3(A_676,B_679,C_678),'#skF_8')
      | ~ m1_subset_1(k13_lattice3(A_676,B_679,C_678),u1_struct_0(A_676))
      | ~ v12_waybel_0('#skF_8',A_676)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ r1_orders_2(A_676,C_678,'#skF_3'('#skF_7','#skF_8',C_675,D_677))
      | ~ r1_orders_2(A_676,B_679,'#skF_3'('#skF_7','#skF_8',C_675,D_677))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8',C_675,D_677),u1_struct_0(A_676))
      | ~ m1_subset_1(C_678,u1_struct_0(A_676))
      | ~ m1_subset_1(B_679,u1_struct_0(A_676))
      | ~ l1_orders_2(A_676)
      | ~ v1_lattice3(A_676)
      | ~ v5_orders_2(A_676)
      | ~ r2_hidden(D_677,'#skF_8')
      | ~ r2_hidden(C_675,'#skF_8')
      | ~ m1_subset_1(D_677,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_675,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2761,c_3562])).

tff(c_5614,plain,(
    ! [C_675,D_677] :
      ( r2_hidden(k13_lattice3('#skF_7','#skF_9','#skF_10'),'#skF_8')
      | ~ v12_waybel_0('#skF_8','#skF_7')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_orders_2('#skF_7','#skF_10','#skF_3'('#skF_7','#skF_8',C_675,D_677))
      | ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8',C_675,D_677))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8',C_675,D_677),u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ v1_lattice3('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ r2_hidden(D_677,'#skF_8')
      | ~ r2_hidden(C_675,'#skF_8')
      | ~ m1_subset_1(D_677,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_675,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4764,c_5598])).

tff(c_5662,plain,(
    ! [C_675,D_677] :
      ( r2_hidden(k13_lattice3('#skF_7','#skF_9','#skF_10'),'#skF_8')
      | ~ r1_orders_2('#skF_7','#skF_10','#skF_3'('#skF_7','#skF_8',C_675,D_677))
      | ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8',C_675,D_677))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8',C_675,D_677),u1_struct_0('#skF_7'))
      | ~ r2_hidden(D_677,'#skF_8')
      | ~ r2_hidden(C_675,'#skF_8')
      | ~ m1_subset_1(D_677,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_675,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2692,c_2694,c_48,c_50,c_5614])).

tff(c_6239,plain,(
    ! [C_691,D_692] :
      ( ~ r1_orders_2('#skF_7','#skF_10','#skF_3'('#skF_7','#skF_8',C_691,D_692))
      | ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8',C_691,D_692))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8',C_691,D_692),u1_struct_0('#skF_7'))
      | ~ r2_hidden(D_692,'#skF_8')
      | ~ r2_hidden(C_691,'#skF_8')
      | ~ m1_subset_1(D_692,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_691,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2696,c_5662])).

tff(c_6243,plain,(
    ! [C_71,D_75] :
      ( ~ r1_orders_2('#skF_7','#skF_10','#skF_3'('#skF_7','#skF_8',C_71,D_75))
      | ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8',C_71,D_75))
      | ~ r2_hidden(D_75,'#skF_8')
      | ~ r2_hidden(C_71,'#skF_8')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_71,u1_struct_0('#skF_7'))
      | ~ v1_waybel_0('#skF_8','#skF_7')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_6239])).

tff(c_9816,plain,(
    ! [C_747,D_748] :
      ( ~ r1_orders_2('#skF_7','#skF_10','#skF_3'('#skF_7','#skF_8',C_747,D_748))
      | ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8',C_747,D_748))
      | ~ r2_hidden(D_748,'#skF_8')
      | ~ r2_hidden(C_747,'#skF_8')
      | ~ m1_subset_1(D_748,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_747,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_2684,c_6243])).

tff(c_9820,plain,(
    ! [D_458] :
      ( ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10',D_458))
      | ~ r2_hidden(D_458,'#skF_8')
      | ~ r2_hidden('#skF_10','#skF_8')
      | ~ m1_subset_1(D_458,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2787,c_9816])).

tff(c_9831,plain,(
    ! [D_749] :
      ( ~ r1_orders_2('#skF_7','#skF_9','#skF_3'('#skF_7','#skF_8','#skF_10',D_749))
      | ~ r2_hidden(D_749,'#skF_8')
      | ~ m1_subset_1(D_749,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2694,c_2683,c_9820])).

tff(c_9835,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2769,c_9831])).

tff(c_9839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2694,c_2692,c_2683,c_2688,c_9835])).

%------------------------------------------------------------------------------
