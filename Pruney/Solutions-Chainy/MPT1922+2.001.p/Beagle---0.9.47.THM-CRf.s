%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:45 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 326 expanded)
%              Number of leaves         :   32 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  197 (1266 expanded)
%              Number of equality atoms :    5 ( 122 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_yellow_6 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_waybel_0(B,A)
           => ! [C] :
                ( m1_yellow_6(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( ( D = F
                                    & E = G
                                    & r1_orders_2(C,F,G) )
                                 => r1_orders_2(B,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(c_32,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ~ r1_orders_2('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    ~ r1_orders_2('#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_48,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_61,plain,(
    ! [B_150,A_151] :
      ( l1_orders_2(B_150)
      | ~ l1_waybel_0(B_150,A_151)
      | ~ l1_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_67,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_44,plain,(
    m1_yellow_6('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_91,plain,(
    ! [C_167,A_168,B_169] :
      ( l1_waybel_0(C_167,A_168)
      | ~ m1_yellow_6(C_167,A_168,B_169)
      | ~ l1_waybel_0(B_169,A_168)
      | ~ l1_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_94,plain,
    ( l1_waybel_0('#skF_4','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_91])).

tff(c_97,plain,(
    l1_waybel_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_94])).

tff(c_18,plain,(
    ! [B_18,A_16] :
      ( l1_orders_2(B_18)
      | ~ l1_waybel_0(B_18,A_16)
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_18])).

tff(c_103,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_154,B_155] :
      ( ~ r2_hidden('#skF_1'(A_154,B_155),B_155)
      | r1_tarski(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_121,plain,(
    ! [B_177,A_178] :
      ( m1_yellow_0(B_177,A_178)
      | ~ r1_tarski(u1_orders_2(B_177),u1_orders_2(A_178))
      | ~ r1_tarski(u1_struct_0(B_177),u1_struct_0(A_178))
      | ~ l1_orders_2(B_177)
      | ~ l1_orders_2(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [B_177] :
      ( m1_yellow_0(B_177,B_177)
      | ~ r1_tarski(u1_orders_2(B_177),u1_orders_2(B_177))
      | ~ l1_orders_2(B_177) ) ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_132,plain,(
    ! [B_177] :
      ( m1_yellow_0(B_177,B_177)
      | ~ l1_orders_2(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_128])).

tff(c_114,plain,(
    ! [C_174,B_175,A_176] :
      ( m1_yellow_0(C_174,B_175)
      | ~ m1_yellow_6(C_174,A_176,B_175)
      | ~ l1_waybel_0(C_174,A_176)
      | ~ l1_waybel_0(B_175,A_176)
      | ~ l1_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_117,plain,
    ( m1_yellow_0('#skF_4','#skF_3')
    | ~ l1_waybel_0('#skF_4','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_114])).

tff(c_120,plain,(
    m1_yellow_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_97,c_117])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( r1_tarski(u1_orders_2(B_15),u1_orders_2(A_13))
      | ~ m1_yellow_0(B_15,A_13)
      | ~ l1_orders_2(B_15)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [C_156,B_157,A_158] :
      ( r2_hidden(C_156,B_157)
      | ~ r2_hidden(C_156,A_158)
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_160,B_161,B_162] :
      ( r2_hidden('#skF_1'(A_160,B_161),B_162)
      | ~ r1_tarski(A_160,B_162)
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_170,B_171,B_172,B_173] :
      ( r2_hidden('#skF_1'(A_170,B_171),B_172)
      | ~ r1_tarski(B_173,B_172)
      | ~ r1_tarski(A_170,B_173)
      | r1_tarski(A_170,B_171) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_160,plain,(
    ! [A_193,B_194,A_195,B_196] :
      ( r2_hidden('#skF_1'(A_193,B_194),u1_orders_2(A_195))
      | ~ r1_tarski(A_193,u1_orders_2(B_196))
      | r1_tarski(A_193,B_194)
      | ~ m1_yellow_0(B_196,A_195)
      | ~ l1_orders_2(B_196)
      | ~ l1_orders_2(A_195) ) ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_210,plain,(
    ! [B_215,B_216,A_217,A_218] :
      ( r2_hidden('#skF_1'(u1_orders_2(B_215),B_216),u1_orders_2(A_217))
      | r1_tarski(u1_orders_2(B_215),B_216)
      | ~ m1_yellow_0(A_218,A_217)
      | ~ l1_orders_2(A_217)
      | ~ m1_yellow_0(B_215,A_218)
      | ~ l1_orders_2(B_215)
      | ~ l1_orders_2(A_218) ) ),
    inference(resolution,[status(thm)],[c_14,c_160])).

tff(c_214,plain,(
    ! [B_215,B_216] :
      ( r2_hidden('#skF_1'(u1_orders_2(B_215),B_216),u1_orders_2('#skF_3'))
      | r1_tarski(u1_orders_2(B_215),B_216)
      | ~ l1_orders_2('#skF_3')
      | ~ m1_yellow_0(B_215,'#skF_4')
      | ~ l1_orders_2(B_215)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_120,c_210])).

tff(c_219,plain,(
    ! [B_219,B_220] :
      ( r2_hidden('#skF_1'(u1_orders_2(B_219),B_220),u1_orders_2('#skF_3'))
      | r1_tarski(u1_orders_2(B_219),B_220)
      | ~ m1_yellow_0(B_219,'#skF_4')
      | ~ l1_orders_2(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_67,c_214])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_227,plain,(
    ! [B_219] :
      ( r1_tarski(u1_orders_2(B_219),u1_orders_2('#skF_3'))
      | ~ m1_yellow_0(B_219,'#skF_4')
      | ~ l1_orders_2(B_219) ) ),
    inference(resolution,[status(thm)],[c_219,c_4])).

tff(c_34,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_49,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    r1_orders_2('#skF_4','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_51,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_134,plain,(
    ! [B_180,C_181,A_182] :
      ( r2_hidden(k4_tarski(B_180,C_181),u1_orders_2(A_182))
      | ~ r1_orders_2(A_182,B_180,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_182))
      | ~ m1_subset_1(B_180,u1_struct_0(A_182))
      | ~ l1_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_202,plain,(
    ! [B_211,C_212,B_213,A_214] :
      ( r2_hidden(k4_tarski(B_211,C_212),B_213)
      | ~ r1_tarski(u1_orders_2(A_214),B_213)
      | ~ r1_orders_2(A_214,B_211,C_212)
      | ~ m1_subset_1(C_212,u1_struct_0(A_214))
      | ~ m1_subset_1(B_211,u1_struct_0(A_214))
      | ~ l1_orders_2(A_214) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_383,plain,(
    ! [B_252,C_253,A_254,B_255] :
      ( r2_hidden(k4_tarski(B_252,C_253),u1_orders_2(A_254))
      | ~ r1_orders_2(B_255,B_252,C_253)
      | ~ m1_subset_1(C_253,u1_struct_0(B_255))
      | ~ m1_subset_1(B_252,u1_struct_0(B_255))
      | ~ m1_yellow_0(B_255,A_254)
      | ~ l1_orders_2(B_255)
      | ~ l1_orders_2(A_254) ) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_385,plain,(
    ! [A_254] :
      ( r2_hidden(k4_tarski('#skF_5','#skF_8'),u1_orders_2(A_254))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ m1_yellow_0('#skF_4',A_254)
      | ~ l1_orders_2('#skF_4')
      | ~ l1_orders_2(A_254) ) ),
    inference(resolution,[status(thm)],[c_51,c_383])).

tff(c_389,plain,(
    ! [A_256] :
      ( r2_hidden(k4_tarski('#skF_5','#skF_8'),u1_orders_2(A_256))
      | ~ m1_yellow_0('#skF_4',A_256)
      | ~ l1_orders_2(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_49,c_36,c_385])).

tff(c_439,plain,(
    ! [B_259,A_260] :
      ( r2_hidden(k4_tarski('#skF_5','#skF_8'),B_259)
      | ~ r1_tarski(u1_orders_2(A_260),B_259)
      | ~ m1_yellow_0('#skF_4',A_260)
      | ~ l1_orders_2(A_260) ) ),
    inference(resolution,[status(thm)],[c_389,c_2])).

tff(c_450,plain,(
    ! [B_219] :
      ( r2_hidden(k4_tarski('#skF_5','#skF_8'),u1_orders_2('#skF_3'))
      | ~ m1_yellow_0('#skF_4',B_219)
      | ~ m1_yellow_0(B_219,'#skF_4')
      | ~ l1_orders_2(B_219) ) ),
    inference(resolution,[status(thm)],[c_227,c_439])).

tff(c_454,plain,(
    ! [B_261] :
      ( ~ m1_yellow_0('#skF_4',B_261)
      | ~ m1_yellow_0(B_261,'#skF_4')
      | ~ l1_orders_2(B_261) ) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_460,plain,
    ( ~ m1_yellow_0('#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_454])).

tff(c_468,plain,(
    ~ m1_yellow_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_460])).

tff(c_474,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_468])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_474])).

tff(c_479,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_8'),u1_orders_2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_8,plain,(
    ! [A_6,B_10,C_12] :
      ( r1_orders_2(A_6,B_10,C_12)
      | ~ r2_hidden(k4_tarski(B_10,C_12),u1_orders_2(A_6))
      | ~ m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(B_10,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_482,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_479,c_8])).

tff(c_487,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_42,c_50,c_482])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:29:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.45  
% 2.98/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.45  %$ r1_orders_2 > m1_yellow_6 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 2.98/1.45  
% 2.98/1.45  %Foreground sorts:
% 2.98/1.45  
% 2.98/1.45  
% 2.98/1.45  %Background operators:
% 2.98/1.45  
% 2.98/1.45  
% 2.98/1.45  %Foreground operators:
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.98/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.98/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.45  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.98/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.98/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.98/1.45  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.98/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.98/1.45  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.45  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.98/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.98/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.98/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.45  
% 3.14/1.47  tff(f_114, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(C, F, G)) => r1_orders_2(B, D, E)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_yellow_6)).
% 3.14/1.47  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 3.14/1.47  tff(f_85, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 3.14/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.14/1.47  tff(f_55, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 3.14/1.47  tff(f_76, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 3.14/1.47  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 3.14/1.47  tff(c_32, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_28, plain, (~r1_orders_2('#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_52, plain, (~r1_orders_2('#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 3.14/1.47  tff(c_48, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_46, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_61, plain, (![B_150, A_151]: (l1_orders_2(B_150) | ~l1_waybel_0(B_150, A_151) | ~l1_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.47  tff(c_64, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_61])).
% 3.14/1.47  tff(c_67, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64])).
% 3.14/1.47  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 3.14/1.47  tff(c_44, plain, (m1_yellow_6('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_91, plain, (![C_167, A_168, B_169]: (l1_waybel_0(C_167, A_168) | ~m1_yellow_6(C_167, A_168, B_169) | ~l1_waybel_0(B_169, A_168) | ~l1_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.47  tff(c_94, plain, (l1_waybel_0('#skF_4', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_91])).
% 3.14/1.47  tff(c_97, plain, (l1_waybel_0('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_94])).
% 3.14/1.47  tff(c_18, plain, (![B_18, A_16]: (l1_orders_2(B_18) | ~l1_waybel_0(B_18, A_16) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.47  tff(c_100, plain, (l1_orders_2('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_97, c_18])).
% 3.14/1.47  tff(c_103, plain, (l1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_100])).
% 3.14/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.47  tff(c_69, plain, (![A_154, B_155]: (~r2_hidden('#skF_1'(A_154, B_155), B_155) | r1_tarski(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.47  tff(c_74, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_69])).
% 3.14/1.47  tff(c_121, plain, (![B_177, A_178]: (m1_yellow_0(B_177, A_178) | ~r1_tarski(u1_orders_2(B_177), u1_orders_2(A_178)) | ~r1_tarski(u1_struct_0(B_177), u1_struct_0(A_178)) | ~l1_orders_2(B_177) | ~l1_orders_2(A_178))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.14/1.47  tff(c_128, plain, (![B_177]: (m1_yellow_0(B_177, B_177) | ~r1_tarski(u1_orders_2(B_177), u1_orders_2(B_177)) | ~l1_orders_2(B_177))), inference(resolution, [status(thm)], [c_74, c_121])).
% 3.14/1.47  tff(c_132, plain, (![B_177]: (m1_yellow_0(B_177, B_177) | ~l1_orders_2(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_128])).
% 3.14/1.47  tff(c_114, plain, (![C_174, B_175, A_176]: (m1_yellow_0(C_174, B_175) | ~m1_yellow_6(C_174, A_176, B_175) | ~l1_waybel_0(C_174, A_176) | ~l1_waybel_0(B_175, A_176) | ~l1_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.14/1.47  tff(c_117, plain, (m1_yellow_0('#skF_4', '#skF_3') | ~l1_waybel_0('#skF_4', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_114])).
% 3.14/1.47  tff(c_120, plain, (m1_yellow_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_97, c_117])).
% 3.14/1.47  tff(c_14, plain, (![B_15, A_13]: (r1_tarski(u1_orders_2(B_15), u1_orders_2(A_13)) | ~m1_yellow_0(B_15, A_13) | ~l1_orders_2(B_15) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.14/1.47  tff(c_75, plain, (![C_156, B_157, A_158]: (r2_hidden(C_156, B_157) | ~r2_hidden(C_156, A_158) | ~r1_tarski(A_158, B_157))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.47  tff(c_80, plain, (![A_160, B_161, B_162]: (r2_hidden('#skF_1'(A_160, B_161), B_162) | ~r1_tarski(A_160, B_162) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_6, c_75])).
% 3.14/1.47  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.47  tff(c_104, plain, (![A_170, B_171, B_172, B_173]: (r2_hidden('#skF_1'(A_170, B_171), B_172) | ~r1_tarski(B_173, B_172) | ~r1_tarski(A_170, B_173) | r1_tarski(A_170, B_171))), inference(resolution, [status(thm)], [c_80, c_2])).
% 3.14/1.47  tff(c_160, plain, (![A_193, B_194, A_195, B_196]: (r2_hidden('#skF_1'(A_193, B_194), u1_orders_2(A_195)) | ~r1_tarski(A_193, u1_orders_2(B_196)) | r1_tarski(A_193, B_194) | ~m1_yellow_0(B_196, A_195) | ~l1_orders_2(B_196) | ~l1_orders_2(A_195))), inference(resolution, [status(thm)], [c_14, c_104])).
% 3.14/1.47  tff(c_210, plain, (![B_215, B_216, A_217, A_218]: (r2_hidden('#skF_1'(u1_orders_2(B_215), B_216), u1_orders_2(A_217)) | r1_tarski(u1_orders_2(B_215), B_216) | ~m1_yellow_0(A_218, A_217) | ~l1_orders_2(A_217) | ~m1_yellow_0(B_215, A_218) | ~l1_orders_2(B_215) | ~l1_orders_2(A_218))), inference(resolution, [status(thm)], [c_14, c_160])).
% 3.14/1.47  tff(c_214, plain, (![B_215, B_216]: (r2_hidden('#skF_1'(u1_orders_2(B_215), B_216), u1_orders_2('#skF_3')) | r1_tarski(u1_orders_2(B_215), B_216) | ~l1_orders_2('#skF_3') | ~m1_yellow_0(B_215, '#skF_4') | ~l1_orders_2(B_215) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_120, c_210])).
% 3.14/1.47  tff(c_219, plain, (![B_219, B_220]: (r2_hidden('#skF_1'(u1_orders_2(B_219), B_220), u1_orders_2('#skF_3')) | r1_tarski(u1_orders_2(B_219), B_220) | ~m1_yellow_0(B_219, '#skF_4') | ~l1_orders_2(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_67, c_214])).
% 3.14/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.47  tff(c_227, plain, (![B_219]: (r1_tarski(u1_orders_2(B_219), u1_orders_2('#skF_3')) | ~m1_yellow_0(B_219, '#skF_4') | ~l1_orders_2(B_219))), inference(resolution, [status(thm)], [c_219, c_4])).
% 3.14/1.47  tff(c_34, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_49, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.14/1.47  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_30, plain, (r1_orders_2('#skF_4', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.14/1.47  tff(c_51, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 3.14/1.47  tff(c_134, plain, (![B_180, C_181, A_182]: (r2_hidden(k4_tarski(B_180, C_181), u1_orders_2(A_182)) | ~r1_orders_2(A_182, B_180, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_182)) | ~m1_subset_1(B_180, u1_struct_0(A_182)) | ~l1_orders_2(A_182))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.47  tff(c_202, plain, (![B_211, C_212, B_213, A_214]: (r2_hidden(k4_tarski(B_211, C_212), B_213) | ~r1_tarski(u1_orders_2(A_214), B_213) | ~r1_orders_2(A_214, B_211, C_212) | ~m1_subset_1(C_212, u1_struct_0(A_214)) | ~m1_subset_1(B_211, u1_struct_0(A_214)) | ~l1_orders_2(A_214))), inference(resolution, [status(thm)], [c_134, c_2])).
% 3.14/1.47  tff(c_383, plain, (![B_252, C_253, A_254, B_255]: (r2_hidden(k4_tarski(B_252, C_253), u1_orders_2(A_254)) | ~r1_orders_2(B_255, B_252, C_253) | ~m1_subset_1(C_253, u1_struct_0(B_255)) | ~m1_subset_1(B_252, u1_struct_0(B_255)) | ~m1_yellow_0(B_255, A_254) | ~l1_orders_2(B_255) | ~l1_orders_2(A_254))), inference(resolution, [status(thm)], [c_14, c_202])).
% 3.14/1.47  tff(c_385, plain, (![A_254]: (r2_hidden(k4_tarski('#skF_5', '#skF_8'), u1_orders_2(A_254)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_yellow_0('#skF_4', A_254) | ~l1_orders_2('#skF_4') | ~l1_orders_2(A_254))), inference(resolution, [status(thm)], [c_51, c_383])).
% 3.14/1.47  tff(c_389, plain, (![A_256]: (r2_hidden(k4_tarski('#skF_5', '#skF_8'), u1_orders_2(A_256)) | ~m1_yellow_0('#skF_4', A_256) | ~l1_orders_2(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_49, c_36, c_385])).
% 3.14/1.47  tff(c_439, plain, (![B_259, A_260]: (r2_hidden(k4_tarski('#skF_5', '#skF_8'), B_259) | ~r1_tarski(u1_orders_2(A_260), B_259) | ~m1_yellow_0('#skF_4', A_260) | ~l1_orders_2(A_260))), inference(resolution, [status(thm)], [c_389, c_2])).
% 3.14/1.47  tff(c_450, plain, (![B_219]: (r2_hidden(k4_tarski('#skF_5', '#skF_8'), u1_orders_2('#skF_3')) | ~m1_yellow_0('#skF_4', B_219) | ~m1_yellow_0(B_219, '#skF_4') | ~l1_orders_2(B_219))), inference(resolution, [status(thm)], [c_227, c_439])).
% 3.14/1.47  tff(c_454, plain, (![B_261]: (~m1_yellow_0('#skF_4', B_261) | ~m1_yellow_0(B_261, '#skF_4') | ~l1_orders_2(B_261))), inference(splitLeft, [status(thm)], [c_450])).
% 3.14/1.47  tff(c_460, plain, (~m1_yellow_0('#skF_4', '#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_132, c_454])).
% 3.14/1.47  tff(c_468, plain, (~m1_yellow_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_460])).
% 3.14/1.47  tff(c_474, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_132, c_468])).
% 3.14/1.47  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_474])).
% 3.14/1.47  tff(c_479, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_8'), u1_orders_2('#skF_3'))), inference(splitRight, [status(thm)], [c_450])).
% 3.14/1.47  tff(c_8, plain, (![A_6, B_10, C_12]: (r1_orders_2(A_6, B_10, C_12) | ~r2_hidden(k4_tarski(B_10, C_12), u1_orders_2(A_6)) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.47  tff(c_482, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_479, c_8])).
% 3.14/1.47  tff(c_487, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_42, c_50, c_482])).
% 3.14/1.47  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_487])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 96
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 2
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 28
% 3.14/1.47  #Demod        : 42
% 3.14/1.47  #Tautology    : 11
% 3.14/1.47  #SimpNegUnit  : 1
% 3.14/1.47  #BackRed      : 0
% 3.14/1.47  
% 3.14/1.47  #Partial instantiations: 0
% 3.14/1.47  #Strategies tried      : 1
% 3.14/1.47  
% 3.14/1.47  Timing (in seconds)
% 3.14/1.47  ----------------------
% 3.14/1.47  Preprocessing        : 0.33
% 3.14/1.47  Parsing              : 0.17
% 3.14/1.47  CNF conversion       : 0.03
% 3.14/1.48  Main loop            : 0.35
% 3.14/1.48  Inferencing          : 0.13
% 3.14/1.48  Reduction            : 0.09
% 3.14/1.48  Demodulation         : 0.06
% 3.14/1.48  BG Simplification    : 0.02
% 3.14/1.48  Subsumption          : 0.09
% 3.14/1.48  Abstraction          : 0.01
% 3.14/1.48  MUC search           : 0.00
% 3.14/1.48  Cooper               : 0.00
% 3.14/1.48  Total                : 0.73
% 3.14/1.48  Index Insertion      : 0.00
% 3.14/1.48  Index Deletion       : 0.00
% 3.14/1.48  Index Matching       : 0.00
% 3.14/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
