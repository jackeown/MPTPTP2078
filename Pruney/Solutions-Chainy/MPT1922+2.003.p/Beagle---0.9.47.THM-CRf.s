%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:45 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 191 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  191 ( 765 expanded)
%              Number of equality atoms :    5 (  92 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_yellow_6 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_54,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_113,plain,(
    ! [C_190,A_191,B_192] :
      ( l1_waybel_0(C_190,A_191)
      | ~ m1_yellow_6(C_190,A_191,B_192)
      | ~ l1_waybel_0(B_192,A_191)
      | ~ l1_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_116,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_119,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116])).

tff(c_24,plain,(
    ! [B_26,A_24] :
      ( l1_orders_2(B_26)
      | ~ l1_waybel_0(B_26,A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_122,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_119,c_24])).

tff(c_125,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_122])).

tff(c_126,plain,(
    ! [C_193,B_194,A_195] :
      ( m1_yellow_0(C_193,B_194)
      | ~ m1_yellow_6(C_193,A_195,B_194)
      | ~ l1_waybel_0(C_193,A_195)
      | ~ l1_waybel_0(B_194,A_195)
      | ~ l1_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_129,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_126])).

tff(c_132,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_119,c_129])).

tff(c_40,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_55,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_38,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_36,plain,(
    r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_57,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36])).

tff(c_73,plain,(
    ! [B_164,A_165] :
      ( l1_orders_2(B_164)
      | ~ l1_waybel_0(B_164,A_165)
      | ~ l1_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_79,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_76])).

tff(c_34,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_18,plain,(
    ! [B_20,A_18] :
      ( r1_tarski(u1_orders_2(B_20),u1_orders_2(A_18))
      | ~ m1_yellow_0(B_20,A_18)
      | ~ l1_orders_2(B_20)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_237,plain,(
    ! [B_217,C_218,A_219] :
      ( r2_hidden(k4_tarski(B_217,C_218),u1_orders_2(A_219))
      | ~ r1_orders_2(A_219,B_217,C_218)
      | ~ m1_subset_1(C_218,u1_struct_0(A_219))
      | ~ m1_subset_1(B_217,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_174,C_175,B_176] :
      ( m1_subset_1(A_174,C_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(C_175))
      | ~ r2_hidden(A_174,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_174,B_4,A_3] :
      ( m1_subset_1(A_174,B_4)
      | ~ r2_hidden(A_174,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_268,plain,(
    ! [B_237,C_238,B_239,A_240] :
      ( m1_subset_1(k4_tarski(B_237,C_238),B_239)
      | ~ r1_tarski(u1_orders_2(A_240),B_239)
      | ~ r1_orders_2(A_240,B_237,C_238)
      | ~ m1_subset_1(C_238,u1_struct_0(A_240))
      | ~ m1_subset_1(B_237,u1_struct_0(A_240))
      | ~ l1_orders_2(A_240) ) ),
    inference(resolution,[status(thm)],[c_237,c_92])).

tff(c_272,plain,(
    ! [B_241,C_242,A_243,B_244] :
      ( m1_subset_1(k4_tarski(B_241,C_242),u1_orders_2(A_243))
      | ~ r1_orders_2(B_244,B_241,C_242)
      | ~ m1_subset_1(C_242,u1_struct_0(B_244))
      | ~ m1_subset_1(B_241,u1_struct_0(B_244))
      | ~ m1_yellow_0(B_244,A_243)
      | ~ l1_orders_2(B_244)
      | ~ l1_orders_2(A_243) ) ),
    inference(resolution,[status(thm)],[c_18,c_268])).

tff(c_274,plain,(
    ! [A_243] :
      ( m1_subset_1(k4_tarski('#skF_4','#skF_5'),u1_orders_2(A_243))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_yellow_0('#skF_3',A_243)
      | ~ l1_orders_2('#skF_3')
      | ~ l1_orders_2(A_243) ) ),
    inference(resolution,[status(thm)],[c_57,c_272])).

tff(c_278,plain,(
    ! [A_245] :
      ( m1_subset_1(k4_tarski('#skF_4','#skF_5'),u1_orders_2(A_245))
      | ~ m1_yellow_0('#skF_3',A_245)
      | ~ l1_orders_2(A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_55,c_56,c_274])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_210,B_211,C_212] :
      ( r1_orders_2(A_210,B_211,C_212)
      | ~ r2_hidden(k4_tarski(B_211,C_212),u1_orders_2(A_210))
      | ~ m1_subset_1(C_212,u1_struct_0(A_210))
      | ~ m1_subset_1(B_211,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,(
    ! [A_210,B_211,C_212] :
      ( r1_orders_2(A_210,B_211,C_212)
      | ~ m1_subset_1(C_212,u1_struct_0(A_210))
      | ~ m1_subset_1(B_211,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210)
      | v1_xboole_0(u1_orders_2(A_210))
      | ~ m1_subset_1(k4_tarski(B_211,C_212),u1_orders_2(A_210)) ) ),
    inference(resolution,[status(thm)],[c_2,c_168])).

tff(c_293,plain,(
    ! [A_248] :
      ( r1_orders_2(A_248,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_248))
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_248))
      | v1_xboole_0(u1_orders_2(A_248))
      | ~ m1_yellow_0('#skF_3',A_248)
      | ~ l1_orders_2(A_248) ) ),
    inference(resolution,[status(thm)],[c_278,c_172])).

tff(c_296,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_orders_2('#skF_2'))
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_293])).

tff(c_302,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_5')
    | v1_xboole_0(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_132,c_48,c_296])).

tff(c_303,plain,(
    v1_xboole_0(u1_orders_2('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_302])).

tff(c_81,plain,(
    ! [C_168,B_169,A_170] :
      ( ~ v1_xboole_0(C_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(C_168))
      | ~ r2_hidden(A_170,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ! [B_4,A_170,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_170,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_257,plain,(
    ! [B_223,A_224,B_225,C_226] :
      ( ~ v1_xboole_0(B_223)
      | ~ r1_tarski(u1_orders_2(A_224),B_223)
      | ~ r1_orders_2(A_224,B_225,C_226)
      | ~ m1_subset_1(C_226,u1_struct_0(A_224))
      | ~ m1_subset_1(B_225,u1_struct_0(A_224))
      | ~ l1_orders_2(A_224) ) ),
    inference(resolution,[status(thm)],[c_237,c_84])).

tff(c_260,plain,(
    ! [A_18,B_20,B_225,C_226] :
      ( ~ v1_xboole_0(u1_orders_2(A_18))
      | ~ r1_orders_2(B_20,B_225,C_226)
      | ~ m1_subset_1(C_226,u1_struct_0(B_20))
      | ~ m1_subset_1(B_225,u1_struct_0(B_20))
      | ~ m1_yellow_0(B_20,A_18)
      | ~ l1_orders_2(B_20)
      | ~ l1_orders_2(A_18) ) ),
    inference(resolution,[status(thm)],[c_18,c_257])).

tff(c_308,plain,(
    ! [B_20,B_225,C_226] :
      ( ~ r1_orders_2(B_20,B_225,C_226)
      | ~ m1_subset_1(C_226,u1_struct_0(B_20))
      | ~ m1_subset_1(B_225,u1_struct_0(B_20))
      | ~ m1_yellow_0(B_20,'#skF_2')
      | ~ l1_orders_2(B_20)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_303,c_260])).

tff(c_322,plain,(
    ! [B_251,B_252,C_253] :
      ( ~ r1_orders_2(B_251,B_252,C_253)
      | ~ m1_subset_1(C_253,u1_struct_0(B_251))
      | ~ m1_subset_1(B_252,u1_struct_0(B_251))
      | ~ m1_yellow_0(B_251,'#skF_2')
      | ~ l1_orders_2(B_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_308])).

tff(c_324,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_322])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_132,c_55,c_56,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.37  
% 2.30/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.37  %$ r1_orders_2 > m1_yellow_6 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.37  
% 2.63/1.37  %Foreground sorts:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Background operators:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Foreground operators:
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.63/1.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.63/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.37  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.63/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.63/1.37  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.63/1.37  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.37  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.63/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.63/1.37  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.63/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.37  
% 2.63/1.39  tff(f_137, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(C, F, G)) => r1_orders_2(B, D, E)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_yellow_6)).
% 2.63/1.39  tff(f_108, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 2.63/1.39  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.63/1.39  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_yellow_6)).
% 2.63/1.39  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_yellow_0)).
% 2.63/1.39  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.63/1.39  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.63/1.39  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.63/1.39  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.63/1.39  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.63/1.39  tff(c_54, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_52, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_50, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_113, plain, (![C_190, A_191, B_192]: (l1_waybel_0(C_190, A_191) | ~m1_yellow_6(C_190, A_191, B_192) | ~l1_waybel_0(B_192, A_191) | ~l1_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.63/1.39  tff(c_116, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_113])).
% 2.63/1.39  tff(c_119, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116])).
% 2.63/1.39  tff(c_24, plain, (![B_26, A_24]: (l1_orders_2(B_26) | ~l1_waybel_0(B_26, A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.63/1.39  tff(c_122, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_119, c_24])).
% 2.63/1.39  tff(c_125, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_122])).
% 2.63/1.39  tff(c_126, plain, (![C_193, B_194, A_195]: (m1_yellow_0(C_193, B_194) | ~m1_yellow_6(C_193, A_195, B_194) | ~l1_waybel_0(C_193, A_195) | ~l1_waybel_0(B_194, A_195) | ~l1_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.63/1.39  tff(c_129, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_126])).
% 2.63/1.39  tff(c_132, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_119, c_129])).
% 2.63/1.39  tff(c_40, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_55, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 2.63/1.39  tff(c_38, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_56, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 2.63/1.39  tff(c_36, plain, (r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_57, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36])).
% 2.63/1.39  tff(c_73, plain, (![B_164, A_165]: (l1_orders_2(B_164) | ~l1_waybel_0(B_164, A_165) | ~l1_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.63/1.39  tff(c_76, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_73])).
% 2.63/1.39  tff(c_79, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_76])).
% 2.63/1.39  tff(c_34, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.63/1.39  tff(c_18, plain, (![B_20, A_18]: (r1_tarski(u1_orders_2(B_20), u1_orders_2(A_18)) | ~m1_yellow_0(B_20, A_18) | ~l1_orders_2(B_20) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.39  tff(c_237, plain, (![B_217, C_218, A_219]: (r2_hidden(k4_tarski(B_217, C_218), u1_orders_2(A_219)) | ~r1_orders_2(A_219, B_217, C_218) | ~m1_subset_1(C_218, u1_struct_0(A_219)) | ~m1_subset_1(B_217, u1_struct_0(A_219)) | ~l1_orders_2(A_219))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.63/1.39  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.39  tff(c_89, plain, (![A_174, C_175, B_176]: (m1_subset_1(A_174, C_175) | ~m1_subset_1(B_176, k1_zfmisc_1(C_175)) | ~r2_hidden(A_174, B_176))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.39  tff(c_92, plain, (![A_174, B_4, A_3]: (m1_subset_1(A_174, B_4) | ~r2_hidden(A_174, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_89])).
% 2.63/1.39  tff(c_268, plain, (![B_237, C_238, B_239, A_240]: (m1_subset_1(k4_tarski(B_237, C_238), B_239) | ~r1_tarski(u1_orders_2(A_240), B_239) | ~r1_orders_2(A_240, B_237, C_238) | ~m1_subset_1(C_238, u1_struct_0(A_240)) | ~m1_subset_1(B_237, u1_struct_0(A_240)) | ~l1_orders_2(A_240))), inference(resolution, [status(thm)], [c_237, c_92])).
% 2.63/1.39  tff(c_272, plain, (![B_241, C_242, A_243, B_244]: (m1_subset_1(k4_tarski(B_241, C_242), u1_orders_2(A_243)) | ~r1_orders_2(B_244, B_241, C_242) | ~m1_subset_1(C_242, u1_struct_0(B_244)) | ~m1_subset_1(B_241, u1_struct_0(B_244)) | ~m1_yellow_0(B_244, A_243) | ~l1_orders_2(B_244) | ~l1_orders_2(A_243))), inference(resolution, [status(thm)], [c_18, c_268])).
% 2.63/1.39  tff(c_274, plain, (![A_243]: (m1_subset_1(k4_tarski('#skF_4', '#skF_5'), u1_orders_2(A_243)) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_yellow_0('#skF_3', A_243) | ~l1_orders_2('#skF_3') | ~l1_orders_2(A_243))), inference(resolution, [status(thm)], [c_57, c_272])).
% 2.63/1.39  tff(c_278, plain, (![A_245]: (m1_subset_1(k4_tarski('#skF_4', '#skF_5'), u1_orders_2(A_245)) | ~m1_yellow_0('#skF_3', A_245) | ~l1_orders_2(A_245))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_55, c_56, c_274])).
% 2.63/1.39  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.39  tff(c_168, plain, (![A_210, B_211, C_212]: (r1_orders_2(A_210, B_211, C_212) | ~r2_hidden(k4_tarski(B_211, C_212), u1_orders_2(A_210)) | ~m1_subset_1(C_212, u1_struct_0(A_210)) | ~m1_subset_1(B_211, u1_struct_0(A_210)) | ~l1_orders_2(A_210))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.63/1.39  tff(c_172, plain, (![A_210, B_211, C_212]: (r1_orders_2(A_210, B_211, C_212) | ~m1_subset_1(C_212, u1_struct_0(A_210)) | ~m1_subset_1(B_211, u1_struct_0(A_210)) | ~l1_orders_2(A_210) | v1_xboole_0(u1_orders_2(A_210)) | ~m1_subset_1(k4_tarski(B_211, C_212), u1_orders_2(A_210)))), inference(resolution, [status(thm)], [c_2, c_168])).
% 2.63/1.39  tff(c_293, plain, (![A_248]: (r1_orders_2(A_248, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(A_248)) | ~m1_subset_1('#skF_4', u1_struct_0(A_248)) | v1_xboole_0(u1_orders_2(A_248)) | ~m1_yellow_0('#skF_3', A_248) | ~l1_orders_2(A_248))), inference(resolution, [status(thm)], [c_278, c_172])).
% 2.63/1.39  tff(c_296, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_orders_2('#skF_2')) | ~m1_yellow_0('#skF_3', '#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_46, c_293])).
% 2.63/1.39  tff(c_302, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5') | v1_xboole_0(u1_orders_2('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_132, c_48, c_296])).
% 2.63/1.39  tff(c_303, plain, (v1_xboole_0(u1_orders_2('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_302])).
% 2.63/1.39  tff(c_81, plain, (![C_168, B_169, A_170]: (~v1_xboole_0(C_168) | ~m1_subset_1(B_169, k1_zfmisc_1(C_168)) | ~r2_hidden(A_170, B_169))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.39  tff(c_84, plain, (![B_4, A_170, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_170, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.63/1.39  tff(c_257, plain, (![B_223, A_224, B_225, C_226]: (~v1_xboole_0(B_223) | ~r1_tarski(u1_orders_2(A_224), B_223) | ~r1_orders_2(A_224, B_225, C_226) | ~m1_subset_1(C_226, u1_struct_0(A_224)) | ~m1_subset_1(B_225, u1_struct_0(A_224)) | ~l1_orders_2(A_224))), inference(resolution, [status(thm)], [c_237, c_84])).
% 2.63/1.39  tff(c_260, plain, (![A_18, B_20, B_225, C_226]: (~v1_xboole_0(u1_orders_2(A_18)) | ~r1_orders_2(B_20, B_225, C_226) | ~m1_subset_1(C_226, u1_struct_0(B_20)) | ~m1_subset_1(B_225, u1_struct_0(B_20)) | ~m1_yellow_0(B_20, A_18) | ~l1_orders_2(B_20) | ~l1_orders_2(A_18))), inference(resolution, [status(thm)], [c_18, c_257])).
% 2.63/1.39  tff(c_308, plain, (![B_20, B_225, C_226]: (~r1_orders_2(B_20, B_225, C_226) | ~m1_subset_1(C_226, u1_struct_0(B_20)) | ~m1_subset_1(B_225, u1_struct_0(B_20)) | ~m1_yellow_0(B_20, '#skF_2') | ~l1_orders_2(B_20) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_303, c_260])).
% 2.63/1.39  tff(c_322, plain, (![B_251, B_252, C_253]: (~r1_orders_2(B_251, B_252, C_253) | ~m1_subset_1(C_253, u1_struct_0(B_251)) | ~m1_subset_1(B_252, u1_struct_0(B_251)) | ~m1_yellow_0(B_251, '#skF_2') | ~l1_orders_2(B_251))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_308])).
% 2.63/1.39  tff(c_324, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_yellow_0('#skF_3', '#skF_2') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_57, c_322])).
% 2.63/1.39  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_132, c_55, c_56, c_324])).
% 2.63/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  Inference rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Ref     : 0
% 2.63/1.39  #Sup     : 52
% 2.63/1.39  #Fact    : 0
% 2.63/1.39  #Define  : 0
% 2.63/1.39  #Split   : 3
% 2.63/1.39  #Chain   : 0
% 2.63/1.39  #Close   : 0
% 2.63/1.39  
% 2.63/1.39  Ordering : KBO
% 2.63/1.39  
% 2.63/1.39  Simplification rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Subsume      : 0
% 2.63/1.39  #Demod        : 56
% 2.63/1.39  #Tautology    : 22
% 2.63/1.39  #SimpNegUnit  : 1
% 2.63/1.39  #BackRed      : 0
% 2.63/1.39  
% 2.63/1.39  #Partial instantiations: 0
% 2.63/1.39  #Strategies tried      : 1
% 2.63/1.39  
% 2.63/1.39  Timing (in seconds)
% 2.63/1.39  ----------------------
% 2.63/1.40  Preprocessing        : 0.34
% 2.63/1.40  Parsing              : 0.18
% 2.63/1.40  CNF conversion       : 0.03
% 2.63/1.40  Main loop            : 0.24
% 2.63/1.40  Inferencing          : 0.10
% 2.63/1.40  Reduction            : 0.07
% 2.63/1.40  Demodulation         : 0.05
% 2.63/1.40  BG Simplification    : 0.02
% 2.63/1.40  Subsumption          : 0.04
% 2.63/1.40  Abstraction          : 0.01
% 2.63/1.40  MUC search           : 0.00
% 2.63/1.40  Cooper               : 0.00
% 2.63/1.40  Total                : 0.62
% 2.63/1.40  Index Insertion      : 0.00
% 2.63/1.40  Index Deletion       : 0.00
% 2.63/1.40  Index Matching       : 0.00
% 2.63/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
