%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:06 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 227 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  386 (1119 expanded)
%              Number of equality atoms :    4 (  60 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_yellow_0 > m1_subset_1 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ( E = D
                         => ( ( r1_lattice3(B,C,E)
                             => r1_lattice3(A,C,D) )
                            & ( r2_lattice3(B,C,E)
                             => r2_lattice3(A,C,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_yellow_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( ( E = C
                              & F = D
                              & r1_orders_2(B,E,F) )
                           => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_yellow_0)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_40,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_62,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    m1_yellow_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_7')
    | r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_6')
    | r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_46])).

tff(c_63,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_14,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_2'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_2'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_65,plain,(
    ! [A_122,C_123,B_124] :
      ( m1_subset_1(A_122,C_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(C_123))
      | ~ r2_hidden(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_122] :
      ( m1_subset_1(A_122,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_122,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_55,plain,(
    ! [B_120,A_121] :
      ( l1_orders_2(B_120)
      | ~ m1_yellow_0(B_120,A_121)
      | ~ l1_orders_2(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_61,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58])).

tff(c_76,plain,(
    ! [A_144,D_145,C_146,B_147] :
      ( r1_orders_2(A_144,D_145,C_146)
      | ~ r2_hidden(D_145,B_147)
      | ~ m1_subset_1(D_145,u1_struct_0(A_144))
      | ~ r2_lattice3(A_144,B_147,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_182,plain,(
    ! [A_195,C_193,B_194,A_192,C_191] :
      ( r1_orders_2(A_192,'#skF_2'(A_195,B_194,C_191),C_193)
      | ~ m1_subset_1('#skF_2'(A_195,B_194,C_191),u1_struct_0(A_192))
      | ~ r2_lattice3(A_192,B_194,C_193)
      | ~ m1_subset_1(C_193,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192)
      | r2_lattice3(A_195,B_194,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195) ) ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_187,plain,(
    ! [A_195,B_194,C_191,C_193] :
      ( r1_orders_2('#skF_4','#skF_2'(A_195,B_194,C_191),C_193)
      | ~ r2_lattice3('#skF_4',B_194,C_193)
      | ~ m1_subset_1(C_193,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | r2_lattice3(A_195,B_194,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ r2_hidden('#skF_2'(A_195,B_194,C_191),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_182])).

tff(c_217,plain,(
    ! [A_204,B_205,C_206,C_207] :
      ( r1_orders_2('#skF_4','#skF_2'(A_204,B_205,C_206),C_207)
      | ~ r2_lattice3('#skF_4',B_205,C_207)
      | ~ m1_subset_1(C_207,u1_struct_0('#skF_4'))
      | r2_lattice3(A_204,B_205,C_206)
      | ~ m1_subset_1(C_206,u1_struct_0(A_204))
      | ~ l1_orders_2(A_204)
      | ~ r2_hidden('#skF_2'(A_204,B_205,C_206),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_187])).

tff(c_22,plain,(
    ! [A_31,E_91,F_93,B_63] :
      ( r1_orders_2(A_31,E_91,F_93)
      | ~ r1_orders_2(B_63,E_91,F_93)
      | ~ m1_subset_1(F_93,u1_struct_0(B_63))
      | ~ m1_subset_1(E_91,u1_struct_0(B_63))
      | ~ m1_subset_1(F_93,u1_struct_0(A_31))
      | ~ m1_subset_1(E_91,u1_struct_0(A_31))
      | ~ m1_yellow_0(B_63,A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_235,plain,(
    ! [B_212,C_211,A_209,A_210,C_208] :
      ( r1_orders_2(A_210,'#skF_2'(A_209,B_212,C_208),C_211)
      | ~ m1_subset_1('#skF_2'(A_209,B_212,C_208),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_211,u1_struct_0(A_210))
      | ~ m1_subset_1('#skF_2'(A_209,B_212,C_208),u1_struct_0(A_210))
      | ~ m1_yellow_0('#skF_4',A_210)
      | ~ l1_orders_2(A_210)
      | ~ r2_lattice3('#skF_4',B_212,C_211)
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_4'))
      | r2_lattice3(A_209,B_212,C_208)
      | ~ m1_subset_1(C_208,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ r2_hidden('#skF_2'(A_209,B_212,C_208),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_217,c_22])).

tff(c_274,plain,(
    ! [A_241,B_240,C_242,C_239,A_238] :
      ( r1_orders_2(A_238,'#skF_2'(A_241,B_240,C_242),C_239)
      | ~ m1_subset_1(C_239,u1_struct_0(A_238))
      | ~ m1_subset_1('#skF_2'(A_241,B_240,C_242),u1_struct_0(A_238))
      | ~ m1_yellow_0('#skF_4',A_238)
      | ~ l1_orders_2(A_238)
      | ~ r2_lattice3('#skF_4',B_240,C_239)
      | ~ m1_subset_1(C_239,u1_struct_0('#skF_4'))
      | r2_lattice3(A_241,B_240,C_242)
      | ~ m1_subset_1(C_242,u1_struct_0(A_241))
      | ~ l1_orders_2(A_241)
      | ~ r2_hidden('#skF_2'(A_241,B_240,C_242),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_235])).

tff(c_284,plain,(
    ! [A_243,B_244,C_245,C_246] :
      ( r1_orders_2(A_243,'#skF_2'(A_243,B_244,C_245),C_246)
      | ~ m1_subset_1(C_246,u1_struct_0(A_243))
      | ~ m1_yellow_0('#skF_4',A_243)
      | ~ r2_lattice3('#skF_4',B_244,C_246)
      | ~ m1_subset_1(C_246,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(A_243,B_244,C_245),'#skF_5')
      | r2_lattice3(A_243,B_244,C_245)
      | ~ m1_subset_1(C_245,u1_struct_0(A_243))
      | ~ l1_orders_2(A_243) ) ),
    inference(resolution,[status(thm)],[c_16,c_274])).

tff(c_12,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_2'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_298,plain,(
    ! [A_247,B_248,C_249] :
      ( ~ m1_yellow_0('#skF_4',A_247)
      | ~ r2_lattice3('#skF_4',B_248,C_249)
      | ~ m1_subset_1(C_249,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(A_247,B_248,C_249),'#skF_5')
      | r2_lattice3(A_247,B_248,C_249)
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247) ) ),
    inference(resolution,[status(thm)],[c_284,c_12])).

tff(c_304,plain,(
    ! [A_250,C_251] :
      ( ~ m1_yellow_0('#skF_4',A_250)
      | ~ r2_lattice3('#skF_4','#skF_5',C_251)
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_4'))
      | r2_lattice3(A_250,'#skF_5',C_251)
      | ~ m1_subset_1(C_251,u1_struct_0(A_250))
      | ~ l1_orders_2(A_250) ) ),
    inference(resolution,[status(thm)],[c_14,c_298])).

tff(c_314,plain,(
    ! [A_250] :
      ( ~ m1_yellow_0('#skF_4',A_250)
      | ~ r2_lattice3('#skF_4','#skF_5','#skF_6')
      | r2_lattice3(A_250,'#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_250))
      | ~ l1_orders_2(A_250) ) ),
    inference(resolution,[status(thm)],[c_50,c_304])).

tff(c_325,plain,(
    ! [A_252] :
      ( ~ m1_yellow_0('#skF_4',A_252)
      | r2_lattice3(A_252,'#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_252))
      | ~ l1_orders_2(A_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_314])).

tff(c_335,plain,
    ( ~ m1_yellow_0('#skF_4','#skF_3')
    | r2_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_325])).

tff(c_344,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_335])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_344])).

tff(c_348,plain,(
    ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_6')
    | r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_49,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_6')
    | r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_44])).

tff(c_350,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_49])).

tff(c_347,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_hidden('#skF_1'(A_1,B_8,C_9),B_8)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_351,plain,(
    ! [A_253,C_254,B_255] :
      ( m1_subset_1(A_253,C_254)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(C_254))
      | ~ r2_hidden(A_253,B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_354,plain,(
    ! [A_253] :
      ( m1_subset_1(A_253,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_253,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_351])).

tff(c_362,plain,(
    ! [A_275,C_276,D_277,B_278] :
      ( r1_orders_2(A_275,C_276,D_277)
      | ~ r2_hidden(D_277,B_278)
      | ~ m1_subset_1(D_277,u1_struct_0(A_275))
      | ~ r1_lattice3(A_275,B_278,C_276)
      | ~ m1_subset_1(C_276,u1_struct_0(A_275))
      | ~ l1_orders_2(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_407,plain,(
    ! [B_301,A_303,A_304,C_302,C_300] :
      ( r1_orders_2(A_304,C_300,'#skF_1'(A_303,B_301,C_302))
      | ~ m1_subset_1('#skF_1'(A_303,B_301,C_302),u1_struct_0(A_304))
      | ~ r1_lattice3(A_304,B_301,C_300)
      | ~ m1_subset_1(C_300,u1_struct_0(A_304))
      | ~ l1_orders_2(A_304)
      | r1_lattice3(A_303,B_301,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0(A_303))
      | ~ l1_orders_2(A_303) ) ),
    inference(resolution,[status(thm)],[c_6,c_362])).

tff(c_412,plain,(
    ! [C_300,A_303,B_301,C_302] :
      ( r1_orders_2('#skF_4',C_300,'#skF_1'(A_303,B_301,C_302))
      | ~ r1_lattice3('#skF_4',B_301,C_300)
      | ~ m1_subset_1(C_300,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | r1_lattice3(A_303,B_301,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0(A_303))
      | ~ l1_orders_2(A_303)
      | ~ r2_hidden('#skF_1'(A_303,B_301,C_302),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_354,c_407])).

tff(c_431,plain,(
    ! [C_309,A_310,B_311,C_312] :
      ( r1_orders_2('#skF_4',C_309,'#skF_1'(A_310,B_311,C_312))
      | ~ r1_lattice3('#skF_4',B_311,C_309)
      | ~ m1_subset_1(C_309,u1_struct_0('#skF_4'))
      | r1_lattice3(A_310,B_311,C_312)
      | ~ m1_subset_1(C_312,u1_struct_0(A_310))
      | ~ l1_orders_2(A_310)
      | ~ r2_hidden('#skF_1'(A_310,B_311,C_312),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_412])).

tff(c_810,plain,(
    ! [A_470,C_469,B_471,C_468,A_467] :
      ( r1_orders_2(A_467,C_469,'#skF_1'(A_470,B_471,C_468))
      | ~ m1_subset_1('#skF_1'(A_470,B_471,C_468),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_470,B_471,C_468),u1_struct_0(A_467))
      | ~ m1_subset_1(C_469,u1_struct_0(A_467))
      | ~ m1_yellow_0('#skF_4',A_467)
      | ~ l1_orders_2(A_467)
      | ~ r1_lattice3('#skF_4',B_471,C_469)
      | ~ m1_subset_1(C_469,u1_struct_0('#skF_4'))
      | r1_lattice3(A_470,B_471,C_468)
      | ~ m1_subset_1(C_468,u1_struct_0(A_470))
      | ~ l1_orders_2(A_470)
      | ~ r2_hidden('#skF_1'(A_470,B_471,C_468),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_431,c_22])).

tff(c_852,plain,(
    ! [A_482,C_483,B_485,C_481,A_484] :
      ( r1_orders_2(A_484,C_481,'#skF_1'(A_482,B_485,C_483))
      | ~ m1_subset_1('#skF_1'(A_482,B_485,C_483),u1_struct_0(A_484))
      | ~ m1_subset_1(C_481,u1_struct_0(A_484))
      | ~ m1_yellow_0('#skF_4',A_484)
      | ~ l1_orders_2(A_484)
      | ~ r1_lattice3('#skF_4',B_485,C_481)
      | ~ m1_subset_1(C_481,u1_struct_0('#skF_4'))
      | r1_lattice3(A_482,B_485,C_483)
      | ~ m1_subset_1(C_483,u1_struct_0(A_482))
      | ~ l1_orders_2(A_482)
      | ~ r2_hidden('#skF_1'(A_482,B_485,C_483),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_354,c_810])).

tff(c_862,plain,(
    ! [A_486,C_487,B_488,C_489] :
      ( r1_orders_2(A_486,C_487,'#skF_1'(A_486,B_488,C_489))
      | ~ m1_subset_1(C_487,u1_struct_0(A_486))
      | ~ m1_yellow_0('#skF_4',A_486)
      | ~ r1_lattice3('#skF_4',B_488,C_487)
      | ~ m1_subset_1(C_487,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_486,B_488,C_489),'#skF_5')
      | r1_lattice3(A_486,B_488,C_489)
      | ~ m1_subset_1(C_489,u1_struct_0(A_486))
      | ~ l1_orders_2(A_486) ) ),
    inference(resolution,[status(thm)],[c_8,c_852])).

tff(c_4,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_876,plain,(
    ! [A_490,B_491,C_492] :
      ( ~ m1_yellow_0('#skF_4',A_490)
      | ~ r1_lattice3('#skF_4',B_491,C_492)
      | ~ m1_subset_1(C_492,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_490,B_491,C_492),'#skF_5')
      | r1_lattice3(A_490,B_491,C_492)
      | ~ m1_subset_1(C_492,u1_struct_0(A_490))
      | ~ l1_orders_2(A_490) ) ),
    inference(resolution,[status(thm)],[c_862,c_4])).

tff(c_882,plain,(
    ! [A_493,C_494] :
      ( ~ m1_yellow_0('#skF_4',A_493)
      | ~ r1_lattice3('#skF_4','#skF_5',C_494)
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_4'))
      | r1_lattice3(A_493,'#skF_5',C_494)
      | ~ m1_subset_1(C_494,u1_struct_0(A_493))
      | ~ l1_orders_2(A_493) ) ),
    inference(resolution,[status(thm)],[c_6,c_876])).

tff(c_892,plain,(
    ! [A_493] :
      ( ~ m1_yellow_0('#skF_4',A_493)
      | ~ r1_lattice3('#skF_4','#skF_5','#skF_6')
      | r1_lattice3(A_493,'#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_493))
      | ~ l1_orders_2(A_493) ) ),
    inference(resolution,[status(thm)],[c_50,c_882])).

tff(c_903,plain,(
    ! [A_495] :
      ( ~ m1_yellow_0('#skF_4',A_495)
      | r1_lattice3(A_495,'#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_495))
      | ~ l1_orders_2(A_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_892])).

tff(c_913,plain,
    ( ~ m1_yellow_0('#skF_4','#skF_3')
    | r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_903])).

tff(c_922,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_913])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_922])).

tff(c_925,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_926,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_47,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42])).

tff(c_929,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_47])).

tff(c_930,plain,(
    ! [A_496,C_497,B_498] :
      ( m1_subset_1(A_496,C_497)
      | ~ m1_subset_1(B_498,k1_zfmisc_1(C_497))
      | ~ r2_hidden(A_496,B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_933,plain,(
    ! [A_496] :
      ( m1_subset_1(A_496,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_496,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_930])).

tff(c_948,plain,(
    ! [A_522,C_523,D_524,B_525] :
      ( r1_orders_2(A_522,C_523,D_524)
      | ~ r2_hidden(D_524,B_525)
      | ~ m1_subset_1(D_524,u1_struct_0(A_522))
      | ~ r1_lattice3(A_522,B_525,C_523)
      | ~ m1_subset_1(C_523,u1_struct_0(A_522))
      | ~ l1_orders_2(A_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_986,plain,(
    ! [B_543,C_544,A_546,A_547,C_545] :
      ( r1_orders_2(A_547,C_545,'#skF_1'(A_546,B_543,C_544))
      | ~ m1_subset_1('#skF_1'(A_546,B_543,C_544),u1_struct_0(A_547))
      | ~ r1_lattice3(A_547,B_543,C_545)
      | ~ m1_subset_1(C_545,u1_struct_0(A_547))
      | ~ l1_orders_2(A_547)
      | r1_lattice3(A_546,B_543,C_544)
      | ~ m1_subset_1(C_544,u1_struct_0(A_546))
      | ~ l1_orders_2(A_546) ) ),
    inference(resolution,[status(thm)],[c_6,c_948])).

tff(c_991,plain,(
    ! [C_545,A_546,B_543,C_544] :
      ( r1_orders_2('#skF_4',C_545,'#skF_1'(A_546,B_543,C_544))
      | ~ r1_lattice3('#skF_4',B_543,C_545)
      | ~ m1_subset_1(C_545,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | r1_lattice3(A_546,B_543,C_544)
      | ~ m1_subset_1(C_544,u1_struct_0(A_546))
      | ~ l1_orders_2(A_546)
      | ~ r2_hidden('#skF_1'(A_546,B_543,C_544),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_933,c_986])).

tff(c_1010,plain,(
    ! [C_552,A_553,B_554,C_555] :
      ( r1_orders_2('#skF_4',C_552,'#skF_1'(A_553,B_554,C_555))
      | ~ r1_lattice3('#skF_4',B_554,C_552)
      | ~ m1_subset_1(C_552,u1_struct_0('#skF_4'))
      | r1_lattice3(A_553,B_554,C_555)
      | ~ m1_subset_1(C_555,u1_struct_0(A_553))
      | ~ l1_orders_2(A_553)
      | ~ r2_hidden('#skF_1'(A_553,B_554,C_555),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_991])).

tff(c_1329,plain,(
    ! [A_701,B_704,C_703,A_702,C_700] :
      ( r1_orders_2(A_701,C_700,'#skF_1'(A_702,B_704,C_703))
      | ~ m1_subset_1('#skF_1'(A_702,B_704,C_703),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_702,B_704,C_703),u1_struct_0(A_701))
      | ~ m1_subset_1(C_700,u1_struct_0(A_701))
      | ~ m1_yellow_0('#skF_4',A_701)
      | ~ l1_orders_2(A_701)
      | ~ r1_lattice3('#skF_4',B_704,C_700)
      | ~ m1_subset_1(C_700,u1_struct_0('#skF_4'))
      | r1_lattice3(A_702,B_704,C_703)
      | ~ m1_subset_1(C_703,u1_struct_0(A_702))
      | ~ l1_orders_2(A_702)
      | ~ r2_hidden('#skF_1'(A_702,B_704,C_703),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1010,c_22])).

tff(c_1351,plain,(
    ! [B_713,A_712,C_711,C_714,A_710] :
      ( r1_orders_2(A_710,C_714,'#skF_1'(A_712,B_713,C_711))
      | ~ m1_subset_1('#skF_1'(A_712,B_713,C_711),u1_struct_0(A_710))
      | ~ m1_subset_1(C_714,u1_struct_0(A_710))
      | ~ m1_yellow_0('#skF_4',A_710)
      | ~ l1_orders_2(A_710)
      | ~ r1_lattice3('#skF_4',B_713,C_714)
      | ~ m1_subset_1(C_714,u1_struct_0('#skF_4'))
      | r1_lattice3(A_712,B_713,C_711)
      | ~ m1_subset_1(C_711,u1_struct_0(A_712))
      | ~ l1_orders_2(A_712)
      | ~ r2_hidden('#skF_1'(A_712,B_713,C_711),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_933,c_1329])).

tff(c_1361,plain,(
    ! [A_715,C_716,B_717,C_718] :
      ( r1_orders_2(A_715,C_716,'#skF_1'(A_715,B_717,C_718))
      | ~ m1_subset_1(C_716,u1_struct_0(A_715))
      | ~ m1_yellow_0('#skF_4',A_715)
      | ~ r1_lattice3('#skF_4',B_717,C_716)
      | ~ m1_subset_1(C_716,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_715,B_717,C_718),'#skF_5')
      | r1_lattice3(A_715,B_717,C_718)
      | ~ m1_subset_1(C_718,u1_struct_0(A_715))
      | ~ l1_orders_2(A_715) ) ),
    inference(resolution,[status(thm)],[c_8,c_1351])).

tff(c_1375,plain,(
    ! [A_719,B_720,C_721] :
      ( ~ m1_yellow_0('#skF_4',A_719)
      | ~ r1_lattice3('#skF_4',B_720,C_721)
      | ~ m1_subset_1(C_721,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_719,B_720,C_721),'#skF_5')
      | r1_lattice3(A_719,B_720,C_721)
      | ~ m1_subset_1(C_721,u1_struct_0(A_719))
      | ~ l1_orders_2(A_719) ) ),
    inference(resolution,[status(thm)],[c_1361,c_4])).

tff(c_1391,plain,(
    ! [A_727,C_728] :
      ( ~ m1_yellow_0('#skF_4',A_727)
      | ~ r1_lattice3('#skF_4','#skF_5',C_728)
      | ~ m1_subset_1(C_728,u1_struct_0('#skF_4'))
      | r1_lattice3(A_727,'#skF_5',C_728)
      | ~ m1_subset_1(C_728,u1_struct_0(A_727))
      | ~ l1_orders_2(A_727) ) ),
    inference(resolution,[status(thm)],[c_6,c_1375])).

tff(c_1401,plain,(
    ! [A_727] :
      ( ~ m1_yellow_0('#skF_4',A_727)
      | ~ r1_lattice3('#skF_4','#skF_5','#skF_6')
      | r1_lattice3(A_727,'#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_727))
      | ~ l1_orders_2(A_727) ) ),
    inference(resolution,[status(thm)],[c_50,c_1391])).

tff(c_1412,plain,(
    ! [A_729] :
      ( ~ m1_yellow_0('#skF_4',A_729)
      | r1_lattice3(A_729,'#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_729))
      | ~ l1_orders_2(A_729) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_1401])).

tff(c_1422,plain,
    ( ~ m1_yellow_0('#skF_4','#skF_3')
    | r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1412])).

tff(c_1431,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1422])).

tff(c_1433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_925,c_1431])).

%------------------------------------------------------------------------------
