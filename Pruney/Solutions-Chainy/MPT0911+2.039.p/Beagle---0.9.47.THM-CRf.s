%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 400 expanded)
%              Number of leaves         :   26 ( 166 expanded)
%              Depth                    :   18
%              Number of atoms          :  194 (2253 expanded)
%              Number of equality atoms :  148 (1496 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
     => ( ! [F] :
            ( m1_subset_1(F,A)
           => ! [G] :
                ( m1_subset_1(G,B)
               => ! [H] :
                    ( m1_subset_1(H,C)
                   => ( E = k3_mcart_1(F,G,H)
                     => D = F ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_136,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_mcart_1(A_86,B_87,C_88,D_89) = k2_mcart_1(D_89)
      | ~ m1_subset_1(D_89,k3_zfmisc_1(A_86,B_87,C_88))
      | k1_xboole_0 = C_88
      | k1_xboole_0 = B_87
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_142,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_136])).

tff(c_145,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_142])).

tff(c_34,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_147,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_34])).

tff(c_32,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] :
      ( m1_subset_1('#skF_1'(C_29,D_30,E_31,B_28,A_27),A_27)
      | k5_mcart_1(A_27,B_28,C_29,E_31) = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(E_31,k3_zfmisc_1(A_27,B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] :
      ( m1_subset_1('#skF_3'(C_29,D_30,E_31,B_28,A_27),C_29)
      | k5_mcart_1(A_27,B_28,C_29,E_31) = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(E_31,k3_zfmisc_1(A_27,B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] :
      ( m1_subset_1('#skF_2'(C_29,D_30,E_31,B_28,A_27),B_28)
      | k5_mcart_1(A_27,B_28,C_29,E_31) = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(E_31,k3_zfmisc_1(A_27,B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_414,plain,(
    ! [C_165,D_166,A_169,E_167,B_168] :
      ( k3_mcart_1('#skF_1'(C_165,D_166,E_167,B_168,A_169),'#skF_2'(C_165,D_166,E_167,B_168,A_169),'#skF_3'(C_165,D_166,E_167,B_168,A_169)) = E_167
      | k5_mcart_1(A_169,B_168,C_165,E_167) = D_166
      | k1_xboole_0 = C_165
      | k1_xboole_0 = B_168
      | k1_xboole_0 = A_169
      | ~ m1_subset_1(E_167,k3_zfmisc_1(A_169,B_168,C_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    ! [H_56,F_50,G_54] :
      ( H_56 = '#skF_7'
      | k3_mcart_1(F_50,G_54,H_56) != '#skF_8'
      | ~ m1_subset_1(H_56,'#skF_6')
      | ~ m1_subset_1(G_54,'#skF_5')
      | ~ m1_subset_1(F_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_504,plain,(
    ! [D_204,A_203,E_207,B_206,C_205] :
      ( '#skF_3'(C_205,D_204,E_207,B_206,A_203) = '#skF_7'
      | E_207 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(C_205,D_204,E_207,B_206,A_203),'#skF_6')
      | ~ m1_subset_1('#skF_2'(C_205,D_204,E_207,B_206,A_203),'#skF_5')
      | ~ m1_subset_1('#skF_1'(C_205,D_204,E_207,B_206,A_203),'#skF_4')
      | k5_mcart_1(A_203,B_206,C_205,E_207) = D_204
      | k1_xboole_0 = C_205
      | k1_xboole_0 = B_206
      | k1_xboole_0 = A_203
      | ~ m1_subset_1(E_207,k3_zfmisc_1(A_203,B_206,C_205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_42])).

tff(c_508,plain,(
    ! [C_29,D_30,E_31,A_27] :
      ( '#skF_3'(C_29,D_30,E_31,'#skF_5',A_27) = '#skF_7'
      | E_31 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(C_29,D_30,E_31,'#skF_5',A_27),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_29,D_30,E_31,'#skF_5',A_27),'#skF_4')
      | k5_mcart_1(A_27,'#skF_5',C_29,E_31) = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(E_31,k3_zfmisc_1(A_27,'#skF_5',C_29)) ) ),
    inference(resolution,[status(thm)],[c_30,c_504])).

tff(c_548,plain,(
    ! [C_230,D_231,E_232,A_233] :
      ( '#skF_3'(C_230,D_231,E_232,'#skF_5',A_233) = '#skF_7'
      | E_232 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(C_230,D_231,E_232,'#skF_5',A_233),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_230,D_231,E_232,'#skF_5',A_233),'#skF_4')
      | k5_mcart_1(A_233,'#skF_5',C_230,E_232) = D_231
      | k1_xboole_0 = C_230
      | k1_xboole_0 = A_233
      | ~ m1_subset_1(E_232,k3_zfmisc_1(A_233,'#skF_5',C_230)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_508])).

tff(c_552,plain,(
    ! [D_30,E_31,A_27] :
      ( '#skF_3'('#skF_6',D_30,E_31,'#skF_5',A_27) = '#skF_7'
      | E_31 != '#skF_8'
      | ~ m1_subset_1('#skF_1'('#skF_6',D_30,E_31,'#skF_5',A_27),'#skF_4')
      | k5_mcart_1(A_27,'#skF_5','#skF_6',E_31) = D_30
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(E_31,k3_zfmisc_1(A_27,'#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_28,c_548])).

tff(c_557,plain,(
    ! [D_234,E_235,A_236] :
      ( '#skF_3'('#skF_6',D_234,E_235,'#skF_5',A_236) = '#skF_7'
      | E_235 != '#skF_8'
      | ~ m1_subset_1('#skF_1'('#skF_6',D_234,E_235,'#skF_5',A_236),'#skF_4')
      | k5_mcart_1(A_236,'#skF_5','#skF_6',E_235) = D_234
      | k1_xboole_0 = A_236
      | ~ m1_subset_1(E_235,k3_zfmisc_1(A_236,'#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_36,c_552])).

tff(c_561,plain,(
    ! [D_30,E_31] :
      ( '#skF_3'('#skF_6',D_30,E_31,'#skF_5','#skF_4') = '#skF_7'
      | E_31 != '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6',E_31) = D_30
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(E_31,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_32,c_557])).

tff(c_566,plain,(
    ! [D_237,E_238] :
      ( '#skF_3'('#skF_6',D_237,E_238,'#skF_5','#skF_4') = '#skF_7'
      | E_238 != '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6',E_238) = D_237
      | ~ m1_subset_1(E_238,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_40,c_561])).

tff(c_584,plain,(
    ! [D_239] :
      ( '#skF_3'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4') = '#skF_7'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ) ),
    inference(resolution,[status(thm)],[c_44,c_566])).

tff(c_26,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] :
      ( k3_mcart_1('#skF_1'(C_29,D_30,E_31,B_28,A_27),'#skF_2'(C_29,D_30,E_31,B_28,A_27),'#skF_3'(C_29,D_30,E_31,B_28,A_27)) = E_31
      | k5_mcart_1(A_27,B_28,C_29,E_31) = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(E_31,k3_zfmisc_1(A_27,B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_593,plain,(
    ! [D_239] :
      ( k3_mcart_1('#skF_1'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4'),'#skF_2'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4'),'#skF_7') = '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_26])).

tff(c_977,plain,(
    ! [D_239] :
      ( k3_mcart_1('#skF_1'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4'),'#skF_2'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4'),'#skF_7') = '#skF_8'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_593])).

tff(c_978,plain,(
    ! [D_239] :
      ( k3_mcart_1('#skF_1'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4'),'#skF_2'('#skF_6',D_239,'#skF_8','#skF_5','#skF_4'),'#skF_7') = '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_977])).

tff(c_1080,plain,(
    ! [D_2404] :
      ( k3_mcart_1('#skF_1'('#skF_6',D_2404,'#skF_8','#skF_5','#skF_4'),'#skF_2'('#skF_6',D_2404,'#skF_8','#skF_5','#skF_4'),'#skF_7') = '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_2404 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_977])).

tff(c_18,plain,(
    ! [C_19,F_25,B_18,A_17,G_26,E_24] :
      ( k7_mcart_1(A_17,B_18,C_19,k3_mcart_1(E_24,F_25,G_26)) = G_26
      | k1_xboole_0 = C_19
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k3_mcart_1(E_24,F_25,G_26),k3_zfmisc_1(A_17,B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3870,plain,(
    ! [A_13732,B_13733,C_13734,D_13735] :
      ( k7_mcart_1(A_13732,B_13733,C_13734,k3_mcart_1('#skF_1'('#skF_6',D_13735,'#skF_8','#skF_5','#skF_4'),'#skF_2'('#skF_6',D_13735,'#skF_8','#skF_5','#skF_4'),'#skF_7')) = '#skF_7'
      | k1_xboole_0 = C_13734
      | k1_xboole_0 = B_13733
      | k1_xboole_0 = A_13732
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_13732,B_13733,C_13734))
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_13735 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_18])).

tff(c_3879,plain,(
    ! [A_13732,B_13733,C_13734,D_239] :
      ( k7_mcart_1(A_13732,B_13733,C_13734,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_13734
      | k1_xboole_0 = B_13733
      | k1_xboole_0 = A_13732
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_13732,B_13733,C_13734))
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_3870])).

tff(c_3902,plain,(
    ! [D_239] :
      ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ) ),
    inference(splitLeft,[status(thm)],[c_3879])).

tff(c_5298,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(factorization,[status(thm),theory(equality)],[c_3902])).

tff(c_3964,plain,(
    ! [D_239] : k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_239 ),
    inference(factorization,[status(thm),theory(equality)],[c_3902])).

tff(c_5959,plain,(
    ! [D_22206] : D_22206 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_5298,c_3964])).

tff(c_6203,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5959,c_147])).

tff(c_6205,plain,(
    ! [A_24313,B_24314,C_24315] :
      ( k7_mcart_1(A_24313,B_24314,C_24315,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_24315
      | k1_xboole_0 = B_24314
      | k1_xboole_0 = A_24313
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_24313,B_24314,C_24315)) ) ),
    inference(splitRight,[status(thm)],[c_3879])).

tff(c_6212,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_6205])).

tff(c_6214,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_6212])).

tff(c_6216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_147,c_6214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.20  
% 6.09/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.20  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.09/2.20  
% 6.09/2.20  %Foreground sorts:
% 6.09/2.20  
% 6.09/2.20  
% 6.09/2.20  %Background operators:
% 6.09/2.20  
% 6.09/2.20  
% 6.09/2.20  %Foreground operators:
% 6.09/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 6.09/2.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.09/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.09/2.20  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.09/2.20  tff('#skF_7', type, '#skF_7': $i).
% 6.09/2.20  tff('#skF_5', type, '#skF_5': $i).
% 6.09/2.20  tff('#skF_6', type, '#skF_6': $i).
% 6.09/2.20  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.09/2.20  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.09/2.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 6.09/2.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 6.09/2.20  tff('#skF_8', type, '#skF_8': $i).
% 6.09/2.20  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.09/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.09/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.09/2.20  tff('#skF_4', type, '#skF_4': $i).
% 6.09/2.20  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.09/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.09/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.20  
% 6.09/2.21  tff(f_141, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 6.09/2.21  tff(f_49, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.09/2.21  tff(f_117, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 6.09/2.21  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 6.09/2.21  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.09/2.21  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.09/2.21  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.09/2.21  tff(c_44, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.09/2.21  tff(c_136, plain, (![A_86, B_87, C_88, D_89]: (k7_mcart_1(A_86, B_87, C_88, D_89)=k2_mcart_1(D_89) | ~m1_subset_1(D_89, k3_zfmisc_1(A_86, B_87, C_88)) | k1_xboole_0=C_88 | k1_xboole_0=B_87 | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.09/2.21  tff(c_142, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_136])).
% 6.09/2.21  tff(c_145, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_142])).
% 6.09/2.21  tff(c_34, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.09/2.21  tff(c_147, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_34])).
% 6.09/2.21  tff(c_32, plain, (![C_29, D_30, B_28, A_27, E_31]: (m1_subset_1('#skF_1'(C_29, D_30, E_31, B_28, A_27), A_27) | k5_mcart_1(A_27, B_28, C_29, E_31)=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(E_31, k3_zfmisc_1(A_27, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.09/2.21  tff(c_28, plain, (![C_29, D_30, B_28, A_27, E_31]: (m1_subset_1('#skF_3'(C_29, D_30, E_31, B_28, A_27), C_29) | k5_mcart_1(A_27, B_28, C_29, E_31)=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(E_31, k3_zfmisc_1(A_27, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.09/2.21  tff(c_30, plain, (![C_29, D_30, B_28, A_27, E_31]: (m1_subset_1('#skF_2'(C_29, D_30, E_31, B_28, A_27), B_28) | k5_mcart_1(A_27, B_28, C_29, E_31)=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(E_31, k3_zfmisc_1(A_27, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.09/2.21  tff(c_414, plain, (![C_165, D_166, A_169, E_167, B_168]: (k3_mcart_1('#skF_1'(C_165, D_166, E_167, B_168, A_169), '#skF_2'(C_165, D_166, E_167, B_168, A_169), '#skF_3'(C_165, D_166, E_167, B_168, A_169))=E_167 | k5_mcart_1(A_169, B_168, C_165, E_167)=D_166 | k1_xboole_0=C_165 | k1_xboole_0=B_168 | k1_xboole_0=A_169 | ~m1_subset_1(E_167, k3_zfmisc_1(A_169, B_168, C_165)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.09/2.21  tff(c_42, plain, (![H_56, F_50, G_54]: (H_56='#skF_7' | k3_mcart_1(F_50, G_54, H_56)!='#skF_8' | ~m1_subset_1(H_56, '#skF_6') | ~m1_subset_1(G_54, '#skF_5') | ~m1_subset_1(F_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.09/2.21  tff(c_504, plain, (![D_204, A_203, E_207, B_206, C_205]: ('#skF_3'(C_205, D_204, E_207, B_206, A_203)='#skF_7' | E_207!='#skF_8' | ~m1_subset_1('#skF_3'(C_205, D_204, E_207, B_206, A_203), '#skF_6') | ~m1_subset_1('#skF_2'(C_205, D_204, E_207, B_206, A_203), '#skF_5') | ~m1_subset_1('#skF_1'(C_205, D_204, E_207, B_206, A_203), '#skF_4') | k5_mcart_1(A_203, B_206, C_205, E_207)=D_204 | k1_xboole_0=C_205 | k1_xboole_0=B_206 | k1_xboole_0=A_203 | ~m1_subset_1(E_207, k3_zfmisc_1(A_203, B_206, C_205)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_42])).
% 6.09/2.21  tff(c_508, plain, (![C_29, D_30, E_31, A_27]: ('#skF_3'(C_29, D_30, E_31, '#skF_5', A_27)='#skF_7' | E_31!='#skF_8' | ~m1_subset_1('#skF_3'(C_29, D_30, E_31, '#skF_5', A_27), '#skF_6') | ~m1_subset_1('#skF_1'(C_29, D_30, E_31, '#skF_5', A_27), '#skF_4') | k5_mcart_1(A_27, '#skF_5', C_29, E_31)=D_30 | k1_xboole_0=C_29 | k1_xboole_0='#skF_5' | k1_xboole_0=A_27 | ~m1_subset_1(E_31, k3_zfmisc_1(A_27, '#skF_5', C_29)))), inference(resolution, [status(thm)], [c_30, c_504])).
% 6.09/2.21  tff(c_548, plain, (![C_230, D_231, E_232, A_233]: ('#skF_3'(C_230, D_231, E_232, '#skF_5', A_233)='#skF_7' | E_232!='#skF_8' | ~m1_subset_1('#skF_3'(C_230, D_231, E_232, '#skF_5', A_233), '#skF_6') | ~m1_subset_1('#skF_1'(C_230, D_231, E_232, '#skF_5', A_233), '#skF_4') | k5_mcart_1(A_233, '#skF_5', C_230, E_232)=D_231 | k1_xboole_0=C_230 | k1_xboole_0=A_233 | ~m1_subset_1(E_232, k3_zfmisc_1(A_233, '#skF_5', C_230)))), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_508])).
% 6.09/2.21  tff(c_552, plain, (![D_30, E_31, A_27]: ('#skF_3'('#skF_6', D_30, E_31, '#skF_5', A_27)='#skF_7' | E_31!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_6', D_30, E_31, '#skF_5', A_27), '#skF_4') | k5_mcart_1(A_27, '#skF_5', '#skF_6', E_31)=D_30 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_27 | ~m1_subset_1(E_31, k3_zfmisc_1(A_27, '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_28, c_548])).
% 6.09/2.21  tff(c_557, plain, (![D_234, E_235, A_236]: ('#skF_3'('#skF_6', D_234, E_235, '#skF_5', A_236)='#skF_7' | E_235!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_6', D_234, E_235, '#skF_5', A_236), '#skF_4') | k5_mcart_1(A_236, '#skF_5', '#skF_6', E_235)=D_234 | k1_xboole_0=A_236 | ~m1_subset_1(E_235, k3_zfmisc_1(A_236, '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_36, c_552])).
% 6.09/2.21  tff(c_561, plain, (![D_30, E_31]: ('#skF_3'('#skF_6', D_30, E_31, '#skF_5', '#skF_4')='#skF_7' | E_31!='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', E_31)=D_30 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1(E_31, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_32, c_557])).
% 6.09/2.21  tff(c_566, plain, (![D_237, E_238]: ('#skF_3'('#skF_6', D_237, E_238, '#skF_5', '#skF_4')='#skF_7' | E_238!='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', E_238)=D_237 | ~m1_subset_1(E_238, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_40, c_561])).
% 6.09/2.21  tff(c_584, plain, (![D_239]: ('#skF_3'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(resolution, [status(thm)], [c_44, c_566])).
% 6.09/2.21  tff(c_26, plain, (![C_29, D_30, B_28, A_27, E_31]: (k3_mcart_1('#skF_1'(C_29, D_30, E_31, B_28, A_27), '#skF_2'(C_29, D_30, E_31, B_28, A_27), '#skF_3'(C_29, D_30, E_31, B_28, A_27))=E_31 | k5_mcart_1(A_27, B_28, C_29, E_31)=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(E_31, k3_zfmisc_1(A_27, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.09/2.21  tff(c_593, plain, (![D_239]: (k3_mcart_1('#skF_1'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4'), '#skF_2'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4'), '#skF_7')='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(superposition, [status(thm), theory('equality')], [c_584, c_26])).
% 6.09/2.21  tff(c_977, plain, (![D_239]: (k3_mcart_1('#skF_1'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4'), '#skF_2'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4'), '#skF_7')='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_593])).
% 6.09/2.21  tff(c_978, plain, (![D_239]: (k3_mcart_1('#skF_1'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4'), '#skF_2'('#skF_6', D_239, '#skF_8', '#skF_5', '#skF_4'), '#skF_7')='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_977])).
% 6.09/2.21  tff(c_1080, plain, (![D_2404]: (k3_mcart_1('#skF_1'('#skF_6', D_2404, '#skF_8', '#skF_5', '#skF_4'), '#skF_2'('#skF_6', D_2404, '#skF_8', '#skF_5', '#skF_4'), '#skF_7')='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_2404)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_977])).
% 6.09/2.21  tff(c_18, plain, (![C_19, F_25, B_18, A_17, G_26, E_24]: (k7_mcart_1(A_17, B_18, C_19, k3_mcart_1(E_24, F_25, G_26))=G_26 | k1_xboole_0=C_19 | k1_xboole_0=B_18 | k1_xboole_0=A_17 | ~m1_subset_1(k3_mcart_1(E_24, F_25, G_26), k3_zfmisc_1(A_17, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.09/2.21  tff(c_3870, plain, (![A_13732, B_13733, C_13734, D_13735]: (k7_mcart_1(A_13732, B_13733, C_13734, k3_mcart_1('#skF_1'('#skF_6', D_13735, '#skF_8', '#skF_5', '#skF_4'), '#skF_2'('#skF_6', D_13735, '#skF_8', '#skF_5', '#skF_4'), '#skF_7'))='#skF_7' | k1_xboole_0=C_13734 | k1_xboole_0=B_13733 | k1_xboole_0=A_13732 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_13732, B_13733, C_13734)) | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_13735)), inference(superposition, [status(thm), theory('equality')], [c_1080, c_18])).
% 6.09/2.21  tff(c_3879, plain, (![A_13732, B_13733, C_13734, D_239]: (k7_mcart_1(A_13732, B_13733, C_13734, '#skF_8')='#skF_7' | k1_xboole_0=C_13734 | k1_xboole_0=B_13733 | k1_xboole_0=A_13732 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_13732, B_13733, C_13734)) | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239 | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(superposition, [status(thm), theory('equality')], [c_978, c_3870])).
% 6.09/2.21  tff(c_3902, plain, (![D_239]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239 | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(splitLeft, [status(thm)], [c_3879])).
% 6.09/2.21  tff(c_5298, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(factorization, [status(thm), theory('equality')], [c_3902])).
% 6.09/2.21  tff(c_3964, plain, (![D_239]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_239)), inference(factorization, [status(thm), theory('equality')], [c_3902])).
% 6.09/2.21  tff(c_5959, plain, (![D_22206]: (D_22206='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5298, c_3964])).
% 6.09/2.21  tff(c_6203, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5959, c_147])).
% 6.09/2.21  tff(c_6205, plain, (![A_24313, B_24314, C_24315]: (k7_mcart_1(A_24313, B_24314, C_24315, '#skF_8')='#skF_7' | k1_xboole_0=C_24315 | k1_xboole_0=B_24314 | k1_xboole_0=A_24313 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_24313, B_24314, C_24315)))), inference(splitRight, [status(thm)], [c_3879])).
% 6.09/2.21  tff(c_6212, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_6205])).
% 6.09/2.21  tff(c_6214, plain, (k2_mcart_1('#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_6212])).
% 6.09/2.21  tff(c_6216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_147, c_6214])).
% 6.09/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.21  
% 6.09/2.21  Inference rules
% 6.09/2.21  ----------------------
% 6.09/2.21  #Ref     : 0
% 6.09/2.21  #Sup     : 795
% 6.09/2.21  #Fact    : 8
% 6.09/2.21  #Define  : 0
% 6.09/2.21  #Split   : 10
% 6.09/2.21  #Chain   : 0
% 6.09/2.21  #Close   : 0
% 6.09/2.21  
% 6.09/2.21  Ordering : KBO
% 6.09/2.21  
% 6.09/2.21  Simplification rules
% 6.09/2.21  ----------------------
% 6.09/2.21  #Subsume      : 96
% 6.09/2.21  #Demod        : 202
% 6.09/2.21  #Tautology    : 105
% 6.09/2.21  #SimpNegUnit  : 42
% 6.09/2.21  #BackRed      : 2
% 6.09/2.21  
% 6.09/2.21  #Partial instantiations: 8292
% 6.09/2.21  #Strategies tried      : 1
% 6.09/2.21  
% 6.09/2.21  Timing (in seconds)
% 6.09/2.21  ----------------------
% 6.09/2.22  Preprocessing        : 0.35
% 6.09/2.22  Parsing              : 0.17
% 6.09/2.22  CNF conversion       : 0.03
% 6.09/2.22  Main loop            : 1.09
% 6.09/2.22  Inferencing          : 0.58
% 6.09/2.22  Reduction            : 0.24
% 6.09/2.22  Demodulation         : 0.16
% 6.09/2.22  BG Simplification    : 0.05
% 6.09/2.22  Subsumption          : 0.17
% 6.09/2.22  Abstraction          : 0.08
% 6.09/2.22  MUC search           : 0.00
% 6.09/2.22  Cooper               : 0.00
% 6.09/2.22  Total                : 1.47
% 6.09/2.22  Index Insertion      : 0.00
% 6.09/2.22  Index Deletion       : 0.00
% 6.09/2.22  Index Matching       : 0.00
% 6.09/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
