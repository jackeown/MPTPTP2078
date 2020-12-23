%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:17 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 137 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 196 expanded)
%              Number of equality atoms :   60 ( 134 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_104,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_679,plain,(
    ! [A_230,B_231,C_232] :
      ( ~ r1_xboole_0(A_230,B_231)
      | ~ r2_hidden(C_232,B_231)
      | ~ r2_hidden(C_232,A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_682,plain,(
    ! [C_232] : ~ r2_hidden(C_232,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_679])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_587,plain,(
    ! [A_187,B_188] : k1_enumset1(A_187,A_187,B_188) = k2_tarski(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_37,B_38,C_39] : r1_tarski(k1_tarski(A_37),k1_enumset1(A_37,B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_605,plain,(
    ! [A_192,B_193] : r1_tarski(k1_tarski(A_192),k2_tarski(A_192,B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_44])).

tff(c_608,plain,(
    ! [A_7] : r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_605])).

tff(c_289,plain,(
    ! [A_136,B_137,C_138] :
      ( ~ r1_xboole_0(A_136,B_137)
      | ~ r2_hidden(C_138,B_137)
      | ~ r2_hidden(C_138,A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_292,plain,(
    ! [C_138] : ~ r2_hidden(C_138,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_289])).

tff(c_176,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_198,plain,(
    ! [A_77,B_78] : r1_tarski(k1_tarski(A_77),k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_44])).

tff(c_201,plain,(
    ! [A_7] : r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_198])).

tff(c_98,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_103,plain,(
    ! [A_57,B_58] : k1_mcart_1(k4_tarski(A_57,B_58)) = A_57 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_112,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_103])).

tff(c_134,plain,(
    ! [A_61,B_62] : k2_mcart_1(k4_tarski(A_61,B_62)) = B_62 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_143,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_134])).

tff(c_96,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_151,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_143,c_96])).

tff(c_152,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_154,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_98])).

tff(c_274,plain,(
    ! [A_134,B_135] : k2_zfmisc_1(k1_tarski(A_134),k1_tarski(B_135)) = k1_tarski(k4_tarski(A_134,B_135)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    ! [A_35,B_36] :
      ( ~ r1_tarski(A_35,k2_zfmisc_1(A_35,B_36))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_341,plain,(
    ! [A_160,B_161] :
      ( ~ r1_tarski(k1_tarski(A_160),k1_tarski(k4_tarski(A_160,B_161)))
      | k1_tarski(A_160) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_28])).

tff(c_344,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_341])).

tff(c_346,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_344])).

tff(c_14,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_474,plain,(
    ! [C_163,D_166,E_167,A_164,B_165] : k4_enumset1(A_164,A_164,B_165,C_163,D_166,E_167) = k3_enumset1(A_164,B_165,C_163,D_166,E_167) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    ! [H_52,F_48,D_46,C_45,A_43,B_44] : r2_hidden(H_52,k4_enumset1(A_43,B_44,C_45,D_46,H_52,F_48)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_537,plain,(
    ! [A_170,E_173,D_169,B_171,C_172] : r2_hidden(D_169,k3_enumset1(A_170,B_171,C_172,D_169,E_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_54])).

tff(c_541,plain,(
    ! [C_174,A_175,B_176,D_177] : r2_hidden(C_174,k2_enumset1(A_175,B_176,C_174,D_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_537])).

tff(c_545,plain,(
    ! [B_178,A_179,C_180] : r2_hidden(B_178,k1_enumset1(A_179,B_178,C_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_541])).

tff(c_549,plain,(
    ! [A_181,B_182] : r2_hidden(A_181,k2_tarski(A_181,B_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_545])).

tff(c_553,plain,(
    ! [A_183] : r2_hidden(A_183,k1_tarski(A_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_549])).

tff(c_559,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_553])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_559])).

tff(c_562,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_566,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_98])).

tff(c_664,plain,(
    ! [A_228,B_229] : k2_zfmisc_1(k1_tarski(A_228),k1_tarski(B_229)) = k1_tarski(k4_tarski(A_228,B_229)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [A_35,B_36] :
      ( ~ r1_tarski(A_35,k2_zfmisc_1(B_36,A_35))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_747,plain,(
    ! [B_276,A_277] :
      ( ~ r1_tarski(k1_tarski(B_276),k1_tarski(k4_tarski(A_277,B_276)))
      | k1_tarski(B_276) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_26])).

tff(c_750,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_747])).

tff(c_752,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_750])).

tff(c_820,plain,(
    ! [B_281,A_280,C_279,E_283,D_282] : k4_enumset1(A_280,A_280,B_281,C_279,D_282,E_283) = k3_enumset1(A_280,B_281,C_279,D_282,E_283) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [H_52,E_47,F_48,C_45,A_43,B_44] : r2_hidden(H_52,k4_enumset1(A_43,B_44,C_45,H_52,E_47,F_48)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_929,plain,(
    ! [D_285,A_289,E_287,C_286,B_288] : r2_hidden(C_286,k3_enumset1(A_289,B_288,C_286,D_285,E_287)) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_56])).

tff(c_933,plain,(
    ! [B_290,A_291,C_292,D_293] : r2_hidden(B_290,k2_enumset1(A_291,B_290,C_292,D_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_929])).

tff(c_937,plain,(
    ! [A_294,B_295,C_296] : r2_hidden(A_294,k1_enumset1(A_294,B_295,C_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_933])).

tff(c_941,plain,(
    ! [A_297,B_298] : r2_hidden(A_297,k2_tarski(A_297,B_298)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_937])).

tff(c_954,plain,(
    ! [A_305] : r2_hidden(A_305,k1_tarski(A_305)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_941])).

tff(c_960,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_954])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_1
% 3.25/1.50  
% 3.25/1.50  %Foreground sorts:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Background operators:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Foreground operators:
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.25/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.25/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.25/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.50  
% 3.25/1.52  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.25/1.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.25/1.52  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.25/1.52  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.25/1.52  tff(f_102, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.25/1.52  tff(f_142, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.25/1.52  tff(f_132, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.25/1.52  tff(f_104, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 3.25/1.52  tff(f_75, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.25/1.52  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.25/1.52  tff(f_63, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.25/1.52  tff(f_65, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.25/1.52  tff(f_128, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.25/1.52  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.25/1.52  tff(c_679, plain, (![A_230, B_231, C_232]: (~r1_xboole_0(A_230, B_231) | ~r2_hidden(C_232, B_231) | ~r2_hidden(C_232, A_230))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.52  tff(c_682, plain, (![C_232]: (~r2_hidden(C_232, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_679])).
% 3.25/1.52  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.52  tff(c_587, plain, (![A_187, B_188]: (k1_enumset1(A_187, A_187, B_188)=k2_tarski(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.52  tff(c_44, plain, (![A_37, B_38, C_39]: (r1_tarski(k1_tarski(A_37), k1_enumset1(A_37, B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.25/1.52  tff(c_605, plain, (![A_192, B_193]: (r1_tarski(k1_tarski(A_192), k2_tarski(A_192, B_193)))), inference(superposition, [status(thm), theory('equality')], [c_587, c_44])).
% 3.25/1.52  tff(c_608, plain, (![A_7]: (r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_605])).
% 3.25/1.52  tff(c_289, plain, (![A_136, B_137, C_138]: (~r1_xboole_0(A_136, B_137) | ~r2_hidden(C_138, B_137) | ~r2_hidden(C_138, A_136))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.52  tff(c_292, plain, (![C_138]: (~r2_hidden(C_138, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_289])).
% 3.25/1.52  tff(c_176, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.52  tff(c_198, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_44])).
% 3.25/1.52  tff(c_201, plain, (![A_7]: (r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_198])).
% 3.25/1.52  tff(c_98, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.25/1.52  tff(c_103, plain, (![A_57, B_58]: (k1_mcart_1(k4_tarski(A_57, B_58))=A_57)), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.25/1.52  tff(c_112, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_98, c_103])).
% 3.25/1.52  tff(c_134, plain, (![A_61, B_62]: (k2_mcart_1(k4_tarski(A_61, B_62))=B_62)), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.25/1.52  tff(c_143, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_98, c_134])).
% 3.25/1.52  tff(c_96, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.25/1.52  tff(c_151, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_143, c_96])).
% 3.25/1.52  tff(c_152, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_151])).
% 3.25/1.52  tff(c_154, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_98])).
% 3.25/1.52  tff(c_274, plain, (![A_134, B_135]: (k2_zfmisc_1(k1_tarski(A_134), k1_tarski(B_135))=k1_tarski(k4_tarski(A_134, B_135)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.52  tff(c_28, plain, (![A_35, B_36]: (~r1_tarski(A_35, k2_zfmisc_1(A_35, B_36)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.25/1.52  tff(c_341, plain, (![A_160, B_161]: (~r1_tarski(k1_tarski(A_160), k1_tarski(k4_tarski(A_160, B_161))) | k1_tarski(A_160)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_274, c_28])).
% 3.25/1.52  tff(c_344, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_154, c_341])).
% 3.25/1.52  tff(c_346, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_201, c_344])).
% 3.25/1.52  tff(c_14, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.52  tff(c_16, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.25/1.52  tff(c_18, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.25/1.52  tff(c_474, plain, (![C_163, D_166, E_167, A_164, B_165]: (k4_enumset1(A_164, A_164, B_165, C_163, D_166, E_167)=k3_enumset1(A_164, B_165, C_163, D_166, E_167))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.52  tff(c_54, plain, (![H_52, F_48, D_46, C_45, A_43, B_44]: (r2_hidden(H_52, k4_enumset1(A_43, B_44, C_45, D_46, H_52, F_48)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.52  tff(c_537, plain, (![A_170, E_173, D_169, B_171, C_172]: (r2_hidden(D_169, k3_enumset1(A_170, B_171, C_172, D_169, E_173)))), inference(superposition, [status(thm), theory('equality')], [c_474, c_54])).
% 3.25/1.52  tff(c_541, plain, (![C_174, A_175, B_176, D_177]: (r2_hidden(C_174, k2_enumset1(A_175, B_176, C_174, D_177)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_537])).
% 3.25/1.52  tff(c_545, plain, (![B_178, A_179, C_180]: (r2_hidden(B_178, k1_enumset1(A_179, B_178, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_541])).
% 3.25/1.52  tff(c_549, plain, (![A_181, B_182]: (r2_hidden(A_181, k2_tarski(A_181, B_182)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_545])).
% 3.25/1.52  tff(c_553, plain, (![A_183]: (r2_hidden(A_183, k1_tarski(A_183)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_549])).
% 3.25/1.52  tff(c_559, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_346, c_553])).
% 3.25/1.52  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_559])).
% 3.25/1.52  tff(c_562, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_151])).
% 3.25/1.52  tff(c_566, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_562, c_98])).
% 3.25/1.52  tff(c_664, plain, (![A_228, B_229]: (k2_zfmisc_1(k1_tarski(A_228), k1_tarski(B_229))=k1_tarski(k4_tarski(A_228, B_229)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.25/1.52  tff(c_26, plain, (![A_35, B_36]: (~r1_tarski(A_35, k2_zfmisc_1(B_36, A_35)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.25/1.52  tff(c_747, plain, (![B_276, A_277]: (~r1_tarski(k1_tarski(B_276), k1_tarski(k4_tarski(A_277, B_276))) | k1_tarski(B_276)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_664, c_26])).
% 3.25/1.52  tff(c_750, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_566, c_747])).
% 3.25/1.52  tff(c_752, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_608, c_750])).
% 3.25/1.52  tff(c_820, plain, (![B_281, A_280, C_279, E_283, D_282]: (k4_enumset1(A_280, A_280, B_281, C_279, D_282, E_283)=k3_enumset1(A_280, B_281, C_279, D_282, E_283))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.52  tff(c_56, plain, (![H_52, E_47, F_48, C_45, A_43, B_44]: (r2_hidden(H_52, k4_enumset1(A_43, B_44, C_45, H_52, E_47, F_48)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.52  tff(c_929, plain, (![D_285, A_289, E_287, C_286, B_288]: (r2_hidden(C_286, k3_enumset1(A_289, B_288, C_286, D_285, E_287)))), inference(superposition, [status(thm), theory('equality')], [c_820, c_56])).
% 3.25/1.52  tff(c_933, plain, (![B_290, A_291, C_292, D_293]: (r2_hidden(B_290, k2_enumset1(A_291, B_290, C_292, D_293)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_929])).
% 3.25/1.52  tff(c_937, plain, (![A_294, B_295, C_296]: (r2_hidden(A_294, k1_enumset1(A_294, B_295, C_296)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_933])).
% 3.25/1.52  tff(c_941, plain, (![A_297, B_298]: (r2_hidden(A_297, k2_tarski(A_297, B_298)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_937])).
% 3.25/1.52  tff(c_954, plain, (![A_305]: (r2_hidden(A_305, k1_tarski(A_305)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_941])).
% 3.25/1.52  tff(c_960, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_752, c_954])).
% 3.25/1.52  tff(c_962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_682, c_960])).
% 3.25/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.52  
% 3.25/1.52  Inference rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Ref     : 0
% 3.25/1.52  #Sup     : 217
% 3.25/1.52  #Fact    : 0
% 3.25/1.52  #Define  : 0
% 3.25/1.52  #Split   : 2
% 3.25/1.52  #Chain   : 0
% 3.25/1.52  #Close   : 0
% 3.25/1.52  
% 3.25/1.52  Ordering : KBO
% 3.25/1.52  
% 3.25/1.52  Simplification rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Subsume      : 7
% 3.25/1.52  #Demod        : 90
% 3.25/1.52  #Tautology    : 127
% 3.25/1.52  #SimpNegUnit  : 2
% 3.25/1.52  #BackRed      : 5
% 3.25/1.52  
% 3.25/1.52  #Partial instantiations: 0
% 3.25/1.52  #Strategies tried      : 1
% 3.25/1.52  
% 3.25/1.52  Timing (in seconds)
% 3.25/1.52  ----------------------
% 3.25/1.52  Preprocessing        : 0.37
% 3.25/1.52  Parsing              : 0.18
% 3.25/1.52  CNF conversion       : 0.03
% 3.25/1.52  Main loop            : 0.38
% 3.25/1.52  Inferencing          : 0.13
% 3.25/1.52  Reduction            : 0.12
% 3.25/1.52  Demodulation         : 0.09
% 3.25/1.52  BG Simplification    : 0.02
% 3.25/1.52  Subsumption          : 0.08
% 3.25/1.52  Abstraction          : 0.02
% 3.25/1.52  MUC search           : 0.00
% 3.25/1.52  Cooper               : 0.00
% 3.25/1.52  Total                : 0.79
% 3.25/1.52  Index Insertion      : 0.00
% 3.25/1.52  Index Deletion       : 0.00
% 3.25/1.52  Index Matching       : 0.00
% 3.25/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
