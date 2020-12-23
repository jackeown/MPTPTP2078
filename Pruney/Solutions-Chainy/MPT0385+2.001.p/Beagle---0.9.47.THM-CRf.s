%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 17.53s
% Output     : CNFRefutation 17.85s
% Verified   : 
% Statistics : Number of formulae       :  145 (2326 expanded)
%              Number of leaves         :   25 ( 765 expanded)
%              Depth                    :   25
%              Number of atoms          :  304 (6826 expanded)
%              Number of equality atoms :   77 (1755 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_49,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_54,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),k3_tarski('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_264,plain,(
    ! [A_88,C_89] :
      ( r2_hidden('#skF_6'(A_88,k1_setfam_1(A_88),C_89),A_88)
      | r2_hidden(C_89,k1_setfam_1(A_88))
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ! [C_39,D_42,A_27] :
      ( r2_hidden(C_39,D_42)
      | ~ r2_hidden(D_42,A_27)
      | ~ r2_hidden(C_39,k1_setfam_1(A_27))
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12226,plain,(
    ! [C_481,A_482,C_483] :
      ( r2_hidden(C_481,'#skF_6'(A_482,k1_setfam_1(A_482),C_483))
      | ~ r2_hidden(C_481,k1_setfam_1(A_482))
      | r2_hidden(C_483,k1_setfam_1(A_482))
      | k1_xboole_0 = A_482 ) ),
    inference(resolution,[status(thm)],[c_264,c_44])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k3_tarski(A_6))
      | ~ r2_hidden(D_24,A_6)
      | ~ r2_hidden(C_21,D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_284,plain,(
    ! [C_21,A_88,C_89] :
      ( r2_hidden(C_21,k3_tarski(A_88))
      | ~ r2_hidden(C_21,'#skF_6'(A_88,k1_setfam_1(A_88),C_89))
      | r2_hidden(C_89,k1_setfam_1(A_88))
      | k1_xboole_0 = A_88 ) ),
    inference(resolution,[status(thm)],[c_264,c_8])).

tff(c_12282,plain,(
    ! [C_484,A_485,C_486] :
      ( r2_hidden(C_484,k3_tarski(A_485))
      | ~ r2_hidden(C_484,k1_setfam_1(A_485))
      | r2_hidden(C_486,k1_setfam_1(A_485))
      | k1_xboole_0 = A_485 ) ),
    inference(resolution,[status(thm)],[c_12226,c_284])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12385,plain,(
    ! [A_487,A_488,C_489] :
      ( r1_tarski(A_487,k1_setfam_1(A_488))
      | r2_hidden(C_489,k3_tarski(A_488))
      | ~ r2_hidden(C_489,k1_setfam_1(A_488))
      | k1_xboole_0 = A_488 ) ),
    inference(resolution,[status(thm)],[c_12282,c_4])).

tff(c_74,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_1,B_2,B_56] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_56)
      | ~ r1_tarski(A_1,B_56)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [C_61,A_62] :
      ( r2_hidden(C_61,'#skF_5'(A_62,k3_tarski(A_62),C_61))
      | ~ r2_hidden(C_61,k3_tarski(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_5'(k1_xboole_0,k1_xboole_0,C_61))
      | ~ r2_hidden(C_61,k3_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_82])).

tff(c_92,plain,(
    ! [C_61] :
      ( r2_hidden(C_61,'#skF_5'(k1_xboole_0,k1_xboole_0,C_61))
      | ~ r2_hidden(C_61,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_89])).

tff(c_100,plain,(
    ! [A_64,C_65] :
      ( r2_hidden('#skF_5'(A_64,k3_tarski(A_64),C_65),A_64)
      | ~ r2_hidden(C_65,k3_tarski(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_107,plain,(
    ! [C_65] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_65),k1_xboole_0)
      | ~ r2_hidden(C_65,k3_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_111,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_66),k1_xboole_0)
      | ~ r2_hidden(C_66,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_107])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [C_78,B_79] :
      ( r2_hidden('#skF_5'(k1_xboole_0,k1_xboole_0,C_78),B_79)
      | ~ r1_tarski(k1_xboole_0,B_79)
      | ~ r2_hidden(C_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_1353,plain,(
    ! [C_182,B_183,C_184] :
      ( r2_hidden(C_182,k3_tarski(B_183))
      | ~ r2_hidden(C_182,'#skF_5'(k1_xboole_0,k1_xboole_0,C_184))
      | ~ r1_tarski(k1_xboole_0,B_183)
      | ~ r2_hidden(C_184,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_185,c_8])).

tff(c_1450,plain,(
    ! [C_188,B_189] :
      ( r2_hidden(C_188,k3_tarski(B_189))
      | ~ r1_tarski(k1_xboole_0,B_189)
      | ~ r2_hidden(C_188,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_92,c_1353])).

tff(c_1503,plain,(
    ! [A_193,B_194] :
      ( r1_tarski(A_193,k3_tarski(B_194))
      | ~ r1_tarski(k1_xboole_0,B_194)
      | ~ r2_hidden('#skF_1'(A_193,k3_tarski(B_194)),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1450,c_4])).

tff(c_1538,plain,(
    ! [B_196,A_197] :
      ( ~ r1_tarski(k1_xboole_0,B_196)
      | ~ r1_tarski(A_197,k1_xboole_0)
      | r1_tarski(A_197,k3_tarski(B_196)) ) ),
    inference(resolution,[status(thm)],[c_77,c_1503])).

tff(c_1569,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_10')
    | ~ r1_tarski(k1_setfam_1('#skF_10'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1538,c_54])).

tff(c_1665,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1569])).

tff(c_10,plain,(
    ! [A_6,C_21] :
      ( r2_hidden('#skF_5'(A_6,k3_tarski(A_6),C_21),A_6)
      | ~ r2_hidden(C_21,k3_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_131,plain,(
    ! [C_70,D_71,A_72] :
      ( r2_hidden(C_70,D_71)
      | ~ r2_hidden(D_71,A_72)
      | ~ r2_hidden(C_70,k1_setfam_1(A_72))
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2144,plain,(
    ! [C_231,A_232,C_233] :
      ( r2_hidden(C_231,'#skF_5'(A_232,k3_tarski(A_232),C_233))
      | ~ r2_hidden(C_231,k1_setfam_1(A_232))
      | k1_xboole_0 = A_232
      | ~ r2_hidden(C_233,k3_tarski(A_232)) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_108,plain,(
    ! [C_21,A_64,C_65] :
      ( r2_hidden(C_21,k3_tarski(A_64))
      | ~ r2_hidden(C_21,'#skF_5'(A_64,k3_tarski(A_64),C_65))
      | ~ r2_hidden(C_65,k3_tarski(A_64)) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_2539,plain,(
    ! [C_249,A_250,C_251] :
      ( r2_hidden(C_249,k3_tarski(A_250))
      | ~ r2_hidden(C_249,k1_setfam_1(A_250))
      | k1_xboole_0 = A_250
      | ~ r2_hidden(C_251,k3_tarski(A_250)) ) ),
    inference(resolution,[status(thm)],[c_2144,c_108])).

tff(c_2764,plain,(
    ! [C_255,A_256,B_257] :
      ( r2_hidden(C_255,k3_tarski(A_256))
      | ~ r2_hidden(C_255,k1_setfam_1(A_256))
      | k1_xboole_0 = A_256
      | r1_tarski(k3_tarski(A_256),B_257) ) ),
    inference(resolution,[status(thm)],[c_6,c_2539])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( ~ r1_tarski(A_25,k2_zfmisc_1(B_26,A_25))
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2854,plain,(
    ! [A_258,C_259] :
      ( k3_tarski(A_258) = k1_xboole_0
      | r2_hidden(C_259,k3_tarski(A_258))
      | ~ r2_hidden(C_259,k1_setfam_1(A_258))
      | k1_xboole_0 = A_258 ) ),
    inference(resolution,[status(thm)],[c_2764,c_26])).

tff(c_8436,plain,(
    ! [A_399,A_400] :
      ( r1_tarski(A_399,k3_tarski(A_400))
      | k3_tarski(A_400) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_399,k3_tarski(A_400)),k1_setfam_1(A_400))
      | k1_xboole_0 = A_400 ) ),
    inference(resolution,[status(thm)],[c_2854,c_4])).

tff(c_8465,plain,(
    ! [A_401] :
      ( k3_tarski(A_401) = k1_xboole_0
      | k1_xboole_0 = A_401
      | r1_tarski(k1_setfam_1(A_401),k3_tarski(A_401)) ) ),
    inference(resolution,[status(thm)],[c_6,c_8436])).

tff(c_8490,plain,
    ( k3_tarski('#skF_10') = k1_xboole_0
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8465,c_54])).

tff(c_8495,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_8490])).

tff(c_52,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8621,plain,(
    k1_setfam_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8495,c_8495,c_52])).

tff(c_8620,plain,(
    k3_tarski('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8495,c_8495,c_30])).

tff(c_8626,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8620,c_54])).

tff(c_8670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8621,c_8626])).

tff(c_8672,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_8490])).

tff(c_8671,plain,(
    k3_tarski('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8490])).

tff(c_2186,plain,(
    ! [C_231,A_232,C_233] :
      ( r2_hidden(C_231,k3_tarski(A_232))
      | ~ r2_hidden(C_231,k1_setfam_1(A_232))
      | k1_xboole_0 = A_232
      | ~ r2_hidden(C_233,k3_tarski(A_232)) ) ),
    inference(resolution,[status(thm)],[c_2144,c_108])).

tff(c_8773,plain,(
    ! [C_231,C_233] :
      ( r2_hidden(C_231,k3_tarski('#skF_10'))
      | ~ r2_hidden(C_231,k1_setfam_1('#skF_10'))
      | k1_xboole_0 = '#skF_10'
      | ~ r2_hidden(C_233,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8671,c_2186])).

tff(c_8872,plain,(
    ! [C_231,C_233] :
      ( r2_hidden(C_231,k1_xboole_0)
      | ~ r2_hidden(C_231,k1_setfam_1('#skF_10'))
      | k1_xboole_0 = '#skF_10'
      | ~ r2_hidden(C_233,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8671,c_8773])).

tff(c_8873,plain,(
    ! [C_231,C_233] :
      ( r2_hidden(C_231,k1_xboole_0)
      | ~ r2_hidden(C_231,k1_setfam_1('#skF_10'))
      | ~ r2_hidden(C_233,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8672,c_8872])).

tff(c_9260,plain,(
    ! [C_409] : ~ r2_hidden(C_409,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8873])).

tff(c_9431,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_9260])).

tff(c_9229,plain,(
    ! [C_233] : ~ r2_hidden(C_233,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8873])).

tff(c_24,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),'#skF_3'(A_6,B_7))
      | r2_hidden('#skF_4'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_227,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_3'(A_86,B_87),A_86)
      | r2_hidden('#skF_4'(A_86,B_87),B_87)
      | k3_tarski(A_86) = B_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3301,plain,(
    ! [C_270,A_271,B_272] :
      ( r2_hidden(C_270,k3_tarski(A_271))
      | ~ r2_hidden(C_270,'#skF_3'(A_271,B_272))
      | r2_hidden('#skF_4'(A_271,B_272),B_272)
      | k3_tarski(A_271) = B_272 ) ),
    inference(resolution,[status(thm)],[c_227,c_8])).

tff(c_3487,plain,(
    ! [A_278,B_279] :
      ( r2_hidden('#skF_2'(A_278,B_279),k3_tarski(A_278))
      | r2_hidden('#skF_4'(A_278,B_279),B_279)
      | k3_tarski(A_278) = B_279 ) ),
    inference(resolution,[status(thm)],[c_24,c_3301])).

tff(c_3572,plain,(
    ! [B_279] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_279),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_279),B_279)
      | k3_tarski(k1_xboole_0) = B_279 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3487])).

tff(c_3603,plain,(
    ! [B_279] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_279),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_279),B_279)
      | k1_xboole_0 = B_279 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3572])).

tff(c_9249,plain,(
    ! [B_279] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_279),B_279)
      | k1_xboole_0 = B_279 ) ),
    inference(negUnitSimplification,[status(thm)],[c_9229,c_3603])).

tff(c_78,plain,(
    ! [C_58,A_59,D_60] :
      ( r2_hidden(C_58,k3_tarski(A_59))
      | ~ r2_hidden(D_60,A_59)
      | ~ r2_hidden(C_58,D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_152,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,k3_tarski(A_74))
      | ~ r2_hidden(C_73,'#skF_1'(A_74,B_75))
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_992,plain,(
    ! [A_155,B_156,B_157] :
      ( r2_hidden('#skF_1'('#skF_1'(A_155,B_156),B_157),k3_tarski(A_155))
      | r1_tarski(A_155,B_156)
      | r1_tarski('#skF_1'(A_155,B_156),B_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_1012,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(A_155,B_156)
      | r1_tarski('#skF_1'(A_155,B_156),k3_tarski(A_155)) ) ),
    inference(resolution,[status(thm)],[c_992,c_4])).

tff(c_8811,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_10',B_156)
      | r1_tarski('#skF_1'('#skF_10',B_156),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8671,c_1012])).

tff(c_3604,plain,(
    ! [B_280] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_280),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_280),B_280)
      | k1_xboole_0 = B_280 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3572])).

tff(c_4280,plain,(
    ! [B_297,B_298] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_297),B_298)
      | ~ r1_tarski(k1_xboole_0,B_298)
      | r2_hidden('#skF_4'(k1_xboole_0,B_297),B_297)
      | k1_xboole_0 = B_297 ) ),
    inference(resolution,[status(thm)],[c_3604,c_2])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_4'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4335,plain,(
    ! [B_298] :
      ( k3_tarski(k1_xboole_0) = B_298
      | ~ r1_tarski(k1_xboole_0,B_298)
      | r2_hidden('#skF_4'(k1_xboole_0,B_298),B_298)
      | k1_xboole_0 = B_298 ) ),
    inference(resolution,[status(thm)],[c_4280,c_20])).

tff(c_4466,plain,(
    ! [B_299] :
      ( k1_xboole_0 = B_299
      | ~ r1_tarski(k1_xboole_0,B_299)
      | r2_hidden('#skF_4'(k1_xboole_0,B_299),B_299)
      | k1_xboole_0 = B_299 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4335])).

tff(c_4558,plain,(
    ! [B_299,B_2] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_299),B_2)
      | ~ r1_tarski(B_299,B_2)
      | ~ r1_tarski(k1_xboole_0,B_299)
      | k1_xboole_0 = B_299 ) ),
    inference(resolution,[status(thm)],[c_4466,c_2])).

tff(c_9392,plain,(
    ! [B_299] :
      ( ~ r1_tarski(B_299,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_299)
      | k1_xboole_0 = B_299 ) ),
    inference(resolution,[status(thm)],[c_4558,c_9260])).

tff(c_10362,plain,(
    ! [B_427] :
      ( ~ r1_tarski(B_427,k1_xboole_0)
      | k1_xboole_0 = B_427 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9431,c_9392])).

tff(c_10395,plain,(
    ! [B_428] :
      ( '#skF_1'('#skF_10',B_428) = k1_xboole_0
      | r1_tarski('#skF_10',B_428) ) ),
    inference(resolution,[status(thm)],[c_8811,c_10362])).

tff(c_10361,plain,(
    ! [B_299] :
      ( ~ r1_tarski(B_299,k1_xboole_0)
      | k1_xboole_0 = B_299 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9431,c_9392])).

tff(c_10399,plain,
    ( k1_xboole_0 = '#skF_10'
    | '#skF_1'('#skF_10',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10395,c_10361])).

tff(c_10424,plain,(
    '#skF_1'('#skF_10',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8672,c_10399])).

tff(c_10464,plain,
    ( r2_hidden(k1_xboole_0,'#skF_10')
    | r1_tarski('#skF_10',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10424,c_6])).

tff(c_10606,plain,(
    r1_tarski('#skF_10',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10464])).

tff(c_10612,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_10606,c_10361])).

tff(c_10628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8672,c_10612])).

tff(c_10629,plain,(
    r2_hidden(k1_xboole_0,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_10464])).

tff(c_10634,plain,(
    ! [C_39] :
      ( r2_hidden(C_39,k1_xboole_0)
      | ~ r2_hidden(C_39,k1_setfam_1('#skF_10'))
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_10629,c_44])).

tff(c_10653,plain,(
    ! [C_435] : ~ r2_hidden(C_435,k1_setfam_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_8672,c_9229,c_10634])).

tff(c_10794,plain,(
    k1_setfam_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9249,c_10653])).

tff(c_10829,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10794,c_1665])).

tff(c_10832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9431,c_10829])).

tff(c_11005,plain,(
    ! [C_439] :
      ( r2_hidden(C_439,k1_xboole_0)
      | ~ r2_hidden(C_439,k1_setfam_1('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_8873])).

tff(c_11215,plain,(
    ! [B_440] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_10'),B_440),k1_xboole_0)
      | r1_tarski(k1_setfam_1('#skF_10'),B_440) ) ),
    inference(resolution,[status(thm)],[c_6,c_11005])).

tff(c_11240,plain,(
    r1_tarski(k1_setfam_1('#skF_10'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11215,c_4])).

tff(c_11257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1665,c_1665,c_11240])).

tff(c_11259,plain,(
    r1_tarski(k1_setfam_1('#skF_10'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1569])).

tff(c_119,plain,(
    ! [A_67,B_68,B_69] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_69)
      | ~ r1_tarski(A_67,B_69)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_129,plain,(
    ! [A_67,B_68,B_2,B_69] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_2)
      | ~ r1_tarski(B_69,B_2)
      | ~ r1_tarski(A_67,B_69)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_11399,plain,(
    ! [A_446,B_447] :
      ( r2_hidden('#skF_1'(A_446,B_447),k1_xboole_0)
      | ~ r1_tarski(A_446,k1_setfam_1('#skF_10'))
      | r1_tarski(A_446,B_447) ) ),
    inference(resolution,[status(thm)],[c_11259,c_129])).

tff(c_11425,plain,(
    ! [A_446] :
      ( ~ r1_tarski(A_446,k1_setfam_1('#skF_10'))
      | r1_tarski(A_446,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_11399,c_4])).

tff(c_12450,plain,(
    ! [A_487,C_489] :
      ( r1_tarski(A_487,k1_xboole_0)
      | r2_hidden(C_489,k3_tarski('#skF_10'))
      | ~ r2_hidden(C_489,k1_setfam_1('#skF_10'))
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_12385,c_11425])).

tff(c_12474,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_12450])).

tff(c_11258,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_1569])).

tff(c_12618,plain,(
    ~ r1_tarski('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12474,c_11258])).

tff(c_12654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12618])).

tff(c_12655,plain,(
    ! [C_489,A_487] :
      ( r2_hidden(C_489,k3_tarski('#skF_10'))
      | ~ r2_hidden(C_489,k1_setfam_1('#skF_10'))
      | r1_tarski(A_487,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_12450])).

tff(c_12657,plain,(
    ! [A_487] : r1_tarski(A_487,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12655])).

tff(c_12656,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_12450])).

tff(c_11688,plain,(
    ! [C_462,A_463,C_464] :
      ( r2_hidden(C_462,'#skF_5'(A_463,k3_tarski(A_463),C_464))
      | ~ r2_hidden(C_462,k1_setfam_1(A_463))
      | k1_xboole_0 = A_463
      | ~ r2_hidden(C_464,k3_tarski(A_463)) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_11757,plain,(
    ! [C_467,A_468,C_469] :
      ( r2_hidden(C_467,k3_tarski(A_468))
      | ~ r2_hidden(C_467,k1_setfam_1(A_468))
      | k1_xboole_0 = A_468
      | ~ r2_hidden(C_469,k3_tarski(A_468)) ) ),
    inference(resolution,[status(thm)],[c_11688,c_108])).

tff(c_11876,plain,(
    ! [C_470,A_471,B_472] :
      ( r2_hidden(C_470,k3_tarski(A_471))
      | ~ r2_hidden(C_470,k1_setfam_1(A_471))
      | k1_xboole_0 = A_471
      | r1_tarski(k3_tarski(A_471),B_472) ) ),
    inference(resolution,[status(thm)],[c_6,c_11757])).

tff(c_11964,plain,(
    ! [A_473,C_474] :
      ( k3_tarski(A_473) = k1_xboole_0
      | r2_hidden(C_474,k3_tarski(A_473))
      | ~ r2_hidden(C_474,k1_setfam_1(A_473))
      | k1_xboole_0 = A_473 ) ),
    inference(resolution,[status(thm)],[c_11876,c_26])).

tff(c_38314,plain,(
    ! [A_980,A_981] :
      ( r1_tarski(A_980,k3_tarski(A_981))
      | k3_tarski(A_981) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_980,k3_tarski(A_981)),k1_setfam_1(A_981))
      | k1_xboole_0 = A_981 ) ),
    inference(resolution,[status(thm)],[c_11964,c_4])).

tff(c_38523,plain,(
    ! [A_985] :
      ( k3_tarski(A_985) = k1_xboole_0
      | k1_xboole_0 = A_985
      | r1_tarski(k1_setfam_1(A_985),k3_tarski(A_985)) ) ),
    inference(resolution,[status(thm)],[c_6,c_38314])).

tff(c_38540,plain,
    ( k3_tarski('#skF_10') = k1_xboole_0
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_38523,c_54])).

tff(c_38568,plain,(
    k3_tarski('#skF_10') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_12656,c_38540])).

tff(c_38577,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38568,c_54])).

tff(c_38580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12657,c_38577])).

tff(c_38582,plain,(
    ! [C_986] :
      ( r2_hidden(C_986,k3_tarski('#skF_10'))
      | ~ r2_hidden(C_986,k1_setfam_1('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_12655])).

tff(c_38771,plain,(
    ! [A_992] :
      ( r1_tarski(A_992,k3_tarski('#skF_10'))
      | ~ r2_hidden('#skF_1'(A_992,k3_tarski('#skF_10')),k1_setfam_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_38582,c_4])).

tff(c_38786,plain,(
    r1_tarski(k1_setfam_1('#skF_10'),k3_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6,c_38771])).

tff(c_38794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_38786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.53/7.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.53/7.68  
% 17.53/7.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.53/7.68  %$ r2_hidden > r1_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_4
% 17.53/7.68  
% 17.53/7.68  %Foreground sorts:
% 17.53/7.68  
% 17.53/7.68  
% 17.53/7.68  %Background operators:
% 17.53/7.68  
% 17.53/7.68  
% 17.53/7.68  %Foreground operators:
% 17.53/7.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.53/7.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.53/7.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.53/7.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.53/7.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.53/7.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.53/7.68  tff('#skF_10', type, '#skF_10': $i).
% 17.53/7.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.53/7.68  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 17.53/7.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.53/7.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.53/7.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.53/7.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.53/7.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.53/7.68  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 17.53/7.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.53/7.68  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 17.53/7.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.53/7.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.53/7.68  
% 17.85/7.72  tff(f_71, negated_conjecture, ~(![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_setfam_1)).
% 17.85/7.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.85/7.72  tff(f_68, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 17.85/7.72  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 17.85/7.72  tff(f_49, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 17.85/7.72  tff(f_48, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 17.85/7.72  tff(c_54, plain, (~r1_tarski(k1_setfam_1('#skF_10'), k3_tarski('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.85/7.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.85/7.72  tff(c_67, plain, (![A_52, B_53]: (~r2_hidden('#skF_1'(A_52, B_53), B_53) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.85/7.72  tff(c_72, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_67])).
% 17.85/7.72  tff(c_264, plain, (![A_88, C_89]: (r2_hidden('#skF_6'(A_88, k1_setfam_1(A_88), C_89), A_88) | r2_hidden(C_89, k1_setfam_1(A_88)) | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.85/7.72  tff(c_44, plain, (![C_39, D_42, A_27]: (r2_hidden(C_39, D_42) | ~r2_hidden(D_42, A_27) | ~r2_hidden(C_39, k1_setfam_1(A_27)) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.85/7.72  tff(c_12226, plain, (![C_481, A_482, C_483]: (r2_hidden(C_481, '#skF_6'(A_482, k1_setfam_1(A_482), C_483)) | ~r2_hidden(C_481, k1_setfam_1(A_482)) | r2_hidden(C_483, k1_setfam_1(A_482)) | k1_xboole_0=A_482)), inference(resolution, [status(thm)], [c_264, c_44])).
% 17.85/7.72  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k3_tarski(A_6)) | ~r2_hidden(D_24, A_6) | ~r2_hidden(C_21, D_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_284, plain, (![C_21, A_88, C_89]: (r2_hidden(C_21, k3_tarski(A_88)) | ~r2_hidden(C_21, '#skF_6'(A_88, k1_setfam_1(A_88), C_89)) | r2_hidden(C_89, k1_setfam_1(A_88)) | k1_xboole_0=A_88)), inference(resolution, [status(thm)], [c_264, c_8])).
% 17.85/7.72  tff(c_12282, plain, (![C_484, A_485, C_486]: (r2_hidden(C_484, k3_tarski(A_485)) | ~r2_hidden(C_484, k1_setfam_1(A_485)) | r2_hidden(C_486, k1_setfam_1(A_485)) | k1_xboole_0=A_485)), inference(resolution, [status(thm)], [c_12226, c_284])).
% 17.85/7.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.85/7.72  tff(c_12385, plain, (![A_487, A_488, C_489]: (r1_tarski(A_487, k1_setfam_1(A_488)) | r2_hidden(C_489, k3_tarski(A_488)) | ~r2_hidden(C_489, k1_setfam_1(A_488)) | k1_xboole_0=A_488)), inference(resolution, [status(thm)], [c_12282, c_4])).
% 17.85/7.72  tff(c_74, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.85/7.72  tff(c_77, plain, (![A_1, B_2, B_56]: (r2_hidden('#skF_1'(A_1, B_2), B_56) | ~r1_tarski(A_1, B_56) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_74])).
% 17.85/7.72  tff(c_30, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.85/7.72  tff(c_82, plain, (![C_61, A_62]: (r2_hidden(C_61, '#skF_5'(A_62, k3_tarski(A_62), C_61)) | ~r2_hidden(C_61, k3_tarski(A_62)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_89, plain, (![C_61]: (r2_hidden(C_61, '#skF_5'(k1_xboole_0, k1_xboole_0, C_61)) | ~r2_hidden(C_61, k3_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_82])).
% 17.85/7.72  tff(c_92, plain, (![C_61]: (r2_hidden(C_61, '#skF_5'(k1_xboole_0, k1_xboole_0, C_61)) | ~r2_hidden(C_61, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_89])).
% 17.85/7.72  tff(c_100, plain, (![A_64, C_65]: (r2_hidden('#skF_5'(A_64, k3_tarski(A_64), C_65), A_64) | ~r2_hidden(C_65, k3_tarski(A_64)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_107, plain, (![C_65]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_65), k1_xboole_0) | ~r2_hidden(C_65, k3_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_100])).
% 17.85/7.72  tff(c_111, plain, (![C_66]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_66), k1_xboole_0) | ~r2_hidden(C_66, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_107])).
% 17.85/7.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.85/7.72  tff(c_185, plain, (![C_78, B_79]: (r2_hidden('#skF_5'(k1_xboole_0, k1_xboole_0, C_78), B_79) | ~r1_tarski(k1_xboole_0, B_79) | ~r2_hidden(C_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_111, c_2])).
% 17.85/7.72  tff(c_1353, plain, (![C_182, B_183, C_184]: (r2_hidden(C_182, k3_tarski(B_183)) | ~r2_hidden(C_182, '#skF_5'(k1_xboole_0, k1_xboole_0, C_184)) | ~r1_tarski(k1_xboole_0, B_183) | ~r2_hidden(C_184, k1_xboole_0))), inference(resolution, [status(thm)], [c_185, c_8])).
% 17.85/7.72  tff(c_1450, plain, (![C_188, B_189]: (r2_hidden(C_188, k3_tarski(B_189)) | ~r1_tarski(k1_xboole_0, B_189) | ~r2_hidden(C_188, k1_xboole_0))), inference(resolution, [status(thm)], [c_92, c_1353])).
% 17.85/7.72  tff(c_1503, plain, (![A_193, B_194]: (r1_tarski(A_193, k3_tarski(B_194)) | ~r1_tarski(k1_xboole_0, B_194) | ~r2_hidden('#skF_1'(A_193, k3_tarski(B_194)), k1_xboole_0))), inference(resolution, [status(thm)], [c_1450, c_4])).
% 17.85/7.72  tff(c_1538, plain, (![B_196, A_197]: (~r1_tarski(k1_xboole_0, B_196) | ~r1_tarski(A_197, k1_xboole_0) | r1_tarski(A_197, k3_tarski(B_196)))), inference(resolution, [status(thm)], [c_77, c_1503])).
% 17.85/7.72  tff(c_1569, plain, (~r1_tarski(k1_xboole_0, '#skF_10') | ~r1_tarski(k1_setfam_1('#skF_10'), k1_xboole_0)), inference(resolution, [status(thm)], [c_1538, c_54])).
% 17.85/7.72  tff(c_1665, plain, (~r1_tarski(k1_setfam_1('#skF_10'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1569])).
% 17.85/7.72  tff(c_10, plain, (![A_6, C_21]: (r2_hidden('#skF_5'(A_6, k3_tarski(A_6), C_21), A_6) | ~r2_hidden(C_21, k3_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_131, plain, (![C_70, D_71, A_72]: (r2_hidden(C_70, D_71) | ~r2_hidden(D_71, A_72) | ~r2_hidden(C_70, k1_setfam_1(A_72)) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.85/7.72  tff(c_2144, plain, (![C_231, A_232, C_233]: (r2_hidden(C_231, '#skF_5'(A_232, k3_tarski(A_232), C_233)) | ~r2_hidden(C_231, k1_setfam_1(A_232)) | k1_xboole_0=A_232 | ~r2_hidden(C_233, k3_tarski(A_232)))), inference(resolution, [status(thm)], [c_10, c_131])).
% 17.85/7.72  tff(c_108, plain, (![C_21, A_64, C_65]: (r2_hidden(C_21, k3_tarski(A_64)) | ~r2_hidden(C_21, '#skF_5'(A_64, k3_tarski(A_64), C_65)) | ~r2_hidden(C_65, k3_tarski(A_64)))), inference(resolution, [status(thm)], [c_100, c_8])).
% 17.85/7.72  tff(c_2539, plain, (![C_249, A_250, C_251]: (r2_hidden(C_249, k3_tarski(A_250)) | ~r2_hidden(C_249, k1_setfam_1(A_250)) | k1_xboole_0=A_250 | ~r2_hidden(C_251, k3_tarski(A_250)))), inference(resolution, [status(thm)], [c_2144, c_108])).
% 17.85/7.72  tff(c_2764, plain, (![C_255, A_256, B_257]: (r2_hidden(C_255, k3_tarski(A_256)) | ~r2_hidden(C_255, k1_setfam_1(A_256)) | k1_xboole_0=A_256 | r1_tarski(k3_tarski(A_256), B_257))), inference(resolution, [status(thm)], [c_6, c_2539])).
% 17.85/7.72  tff(c_26, plain, (![A_25, B_26]: (~r1_tarski(A_25, k2_zfmisc_1(B_26, A_25)) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_48])).
% 17.85/7.72  tff(c_2854, plain, (![A_258, C_259]: (k3_tarski(A_258)=k1_xboole_0 | r2_hidden(C_259, k3_tarski(A_258)) | ~r2_hidden(C_259, k1_setfam_1(A_258)) | k1_xboole_0=A_258)), inference(resolution, [status(thm)], [c_2764, c_26])).
% 17.85/7.72  tff(c_8436, plain, (![A_399, A_400]: (r1_tarski(A_399, k3_tarski(A_400)) | k3_tarski(A_400)=k1_xboole_0 | ~r2_hidden('#skF_1'(A_399, k3_tarski(A_400)), k1_setfam_1(A_400)) | k1_xboole_0=A_400)), inference(resolution, [status(thm)], [c_2854, c_4])).
% 17.85/7.72  tff(c_8465, plain, (![A_401]: (k3_tarski(A_401)=k1_xboole_0 | k1_xboole_0=A_401 | r1_tarski(k1_setfam_1(A_401), k3_tarski(A_401)))), inference(resolution, [status(thm)], [c_6, c_8436])).
% 17.85/7.72  tff(c_8490, plain, (k3_tarski('#skF_10')=k1_xboole_0 | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_8465, c_54])).
% 17.85/7.72  tff(c_8495, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_8490])).
% 17.85/7.72  tff(c_52, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.85/7.72  tff(c_8621, plain, (k1_setfam_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_8495, c_8495, c_52])).
% 17.85/7.72  tff(c_8620, plain, (k3_tarski('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_8495, c_8495, c_30])).
% 17.85/7.72  tff(c_8626, plain, (~r1_tarski(k1_setfam_1('#skF_10'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_8620, c_54])).
% 17.85/7.72  tff(c_8670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_8621, c_8626])).
% 17.85/7.72  tff(c_8672, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_8490])).
% 17.85/7.72  tff(c_8671, plain, (k3_tarski('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8490])).
% 17.85/7.72  tff(c_2186, plain, (![C_231, A_232, C_233]: (r2_hidden(C_231, k3_tarski(A_232)) | ~r2_hidden(C_231, k1_setfam_1(A_232)) | k1_xboole_0=A_232 | ~r2_hidden(C_233, k3_tarski(A_232)))), inference(resolution, [status(thm)], [c_2144, c_108])).
% 17.85/7.72  tff(c_8773, plain, (![C_231, C_233]: (r2_hidden(C_231, k3_tarski('#skF_10')) | ~r2_hidden(C_231, k1_setfam_1('#skF_10')) | k1_xboole_0='#skF_10' | ~r2_hidden(C_233, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8671, c_2186])).
% 17.85/7.72  tff(c_8872, plain, (![C_231, C_233]: (r2_hidden(C_231, k1_xboole_0) | ~r2_hidden(C_231, k1_setfam_1('#skF_10')) | k1_xboole_0='#skF_10' | ~r2_hidden(C_233, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8671, c_8773])).
% 17.85/7.72  tff(c_8873, plain, (![C_231, C_233]: (r2_hidden(C_231, k1_xboole_0) | ~r2_hidden(C_231, k1_setfam_1('#skF_10')) | ~r2_hidden(C_233, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_8672, c_8872])).
% 17.85/7.72  tff(c_9260, plain, (![C_409]: (~r2_hidden(C_409, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8873])).
% 17.85/7.72  tff(c_9431, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_9260])).
% 17.85/7.72  tff(c_9229, plain, (![C_233]: (~r2_hidden(C_233, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8873])).
% 17.85/7.72  tff(c_24, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), '#skF_3'(A_6, B_7)) | r2_hidden('#skF_4'(A_6, B_7), B_7) | k3_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_227, plain, (![A_86, B_87]: (r2_hidden('#skF_3'(A_86, B_87), A_86) | r2_hidden('#skF_4'(A_86, B_87), B_87) | k3_tarski(A_86)=B_87)), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_3301, plain, (![C_270, A_271, B_272]: (r2_hidden(C_270, k3_tarski(A_271)) | ~r2_hidden(C_270, '#skF_3'(A_271, B_272)) | r2_hidden('#skF_4'(A_271, B_272), B_272) | k3_tarski(A_271)=B_272)), inference(resolution, [status(thm)], [c_227, c_8])).
% 17.85/7.72  tff(c_3487, plain, (![A_278, B_279]: (r2_hidden('#skF_2'(A_278, B_279), k3_tarski(A_278)) | r2_hidden('#skF_4'(A_278, B_279), B_279) | k3_tarski(A_278)=B_279)), inference(resolution, [status(thm)], [c_24, c_3301])).
% 17.85/7.72  tff(c_3572, plain, (![B_279]: (r2_hidden('#skF_2'(k1_xboole_0, B_279), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_279), B_279) | k3_tarski(k1_xboole_0)=B_279)), inference(superposition, [status(thm), theory('equality')], [c_30, c_3487])).
% 17.85/7.72  tff(c_3603, plain, (![B_279]: (r2_hidden('#skF_2'(k1_xboole_0, B_279), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_279), B_279) | k1_xboole_0=B_279)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3572])).
% 17.85/7.72  tff(c_9249, plain, (![B_279]: (r2_hidden('#skF_4'(k1_xboole_0, B_279), B_279) | k1_xboole_0=B_279)), inference(negUnitSimplification, [status(thm)], [c_9229, c_3603])).
% 17.85/7.72  tff(c_78, plain, (![C_58, A_59, D_60]: (r2_hidden(C_58, k3_tarski(A_59)) | ~r2_hidden(D_60, A_59) | ~r2_hidden(C_58, D_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_152, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, k3_tarski(A_74)) | ~r2_hidden(C_73, '#skF_1'(A_74, B_75)) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_6, c_78])).
% 17.85/7.72  tff(c_992, plain, (![A_155, B_156, B_157]: (r2_hidden('#skF_1'('#skF_1'(A_155, B_156), B_157), k3_tarski(A_155)) | r1_tarski(A_155, B_156) | r1_tarski('#skF_1'(A_155, B_156), B_157))), inference(resolution, [status(thm)], [c_6, c_152])).
% 17.85/7.72  tff(c_1012, plain, (![A_155, B_156]: (r1_tarski(A_155, B_156) | r1_tarski('#skF_1'(A_155, B_156), k3_tarski(A_155)))), inference(resolution, [status(thm)], [c_992, c_4])).
% 17.85/7.72  tff(c_8811, plain, (![B_156]: (r1_tarski('#skF_10', B_156) | r1_tarski('#skF_1'('#skF_10', B_156), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8671, c_1012])).
% 17.85/7.72  tff(c_3604, plain, (![B_280]: (r2_hidden('#skF_2'(k1_xboole_0, B_280), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_280), B_280) | k1_xboole_0=B_280)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3572])).
% 17.85/7.72  tff(c_4280, plain, (![B_297, B_298]: (r2_hidden('#skF_2'(k1_xboole_0, B_297), B_298) | ~r1_tarski(k1_xboole_0, B_298) | r2_hidden('#skF_4'(k1_xboole_0, B_297), B_297) | k1_xboole_0=B_297)), inference(resolution, [status(thm)], [c_3604, c_2])).
% 17.85/7.72  tff(c_20, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_4'(A_6, B_7), B_7) | k3_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.85/7.72  tff(c_4335, plain, (![B_298]: (k3_tarski(k1_xboole_0)=B_298 | ~r1_tarski(k1_xboole_0, B_298) | r2_hidden('#skF_4'(k1_xboole_0, B_298), B_298) | k1_xboole_0=B_298)), inference(resolution, [status(thm)], [c_4280, c_20])).
% 17.85/7.72  tff(c_4466, plain, (![B_299]: (k1_xboole_0=B_299 | ~r1_tarski(k1_xboole_0, B_299) | r2_hidden('#skF_4'(k1_xboole_0, B_299), B_299) | k1_xboole_0=B_299)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4335])).
% 17.85/7.72  tff(c_4558, plain, (![B_299, B_2]: (r2_hidden('#skF_4'(k1_xboole_0, B_299), B_2) | ~r1_tarski(B_299, B_2) | ~r1_tarski(k1_xboole_0, B_299) | k1_xboole_0=B_299)), inference(resolution, [status(thm)], [c_4466, c_2])).
% 17.85/7.72  tff(c_9392, plain, (![B_299]: (~r1_tarski(B_299, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_299) | k1_xboole_0=B_299)), inference(resolution, [status(thm)], [c_4558, c_9260])).
% 17.85/7.72  tff(c_10362, plain, (![B_427]: (~r1_tarski(B_427, k1_xboole_0) | k1_xboole_0=B_427)), inference(demodulation, [status(thm), theory('equality')], [c_9431, c_9392])).
% 17.85/7.72  tff(c_10395, plain, (![B_428]: ('#skF_1'('#skF_10', B_428)=k1_xboole_0 | r1_tarski('#skF_10', B_428))), inference(resolution, [status(thm)], [c_8811, c_10362])).
% 17.85/7.72  tff(c_10361, plain, (![B_299]: (~r1_tarski(B_299, k1_xboole_0) | k1_xboole_0=B_299)), inference(demodulation, [status(thm), theory('equality')], [c_9431, c_9392])).
% 17.85/7.72  tff(c_10399, plain, (k1_xboole_0='#skF_10' | '#skF_1'('#skF_10', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10395, c_10361])).
% 17.85/7.72  tff(c_10424, plain, ('#skF_1'('#skF_10', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8672, c_10399])).
% 17.85/7.72  tff(c_10464, plain, (r2_hidden(k1_xboole_0, '#skF_10') | r1_tarski('#skF_10', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10424, c_6])).
% 17.85/7.72  tff(c_10606, plain, (r1_tarski('#skF_10', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10464])).
% 17.85/7.72  tff(c_10612, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_10606, c_10361])).
% 17.85/7.72  tff(c_10628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8672, c_10612])).
% 17.85/7.72  tff(c_10629, plain, (r2_hidden(k1_xboole_0, '#skF_10')), inference(splitRight, [status(thm)], [c_10464])).
% 17.85/7.72  tff(c_10634, plain, (![C_39]: (r2_hidden(C_39, k1_xboole_0) | ~r2_hidden(C_39, k1_setfam_1('#skF_10')) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_10629, c_44])).
% 17.85/7.72  tff(c_10653, plain, (![C_435]: (~r2_hidden(C_435, k1_setfam_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_8672, c_9229, c_10634])).
% 17.85/7.72  tff(c_10794, plain, (k1_setfam_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_9249, c_10653])).
% 17.85/7.72  tff(c_10829, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10794, c_1665])).
% 17.85/7.72  tff(c_10832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9431, c_10829])).
% 17.85/7.72  tff(c_11005, plain, (![C_439]: (r2_hidden(C_439, k1_xboole_0) | ~r2_hidden(C_439, k1_setfam_1('#skF_10')))), inference(splitRight, [status(thm)], [c_8873])).
% 17.85/7.72  tff(c_11215, plain, (![B_440]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_10'), B_440), k1_xboole_0) | r1_tarski(k1_setfam_1('#skF_10'), B_440))), inference(resolution, [status(thm)], [c_6, c_11005])).
% 17.85/7.72  tff(c_11240, plain, (r1_tarski(k1_setfam_1('#skF_10'), k1_xboole_0)), inference(resolution, [status(thm)], [c_11215, c_4])).
% 17.85/7.72  tff(c_11257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1665, c_1665, c_11240])).
% 17.85/7.72  tff(c_11259, plain, (r1_tarski(k1_setfam_1('#skF_10'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1569])).
% 17.85/7.72  tff(c_119, plain, (![A_67, B_68, B_69]: (r2_hidden('#skF_1'(A_67, B_68), B_69) | ~r1_tarski(A_67, B_69) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_6, c_74])).
% 17.85/7.72  tff(c_129, plain, (![A_67, B_68, B_2, B_69]: (r2_hidden('#skF_1'(A_67, B_68), B_2) | ~r1_tarski(B_69, B_2) | ~r1_tarski(A_67, B_69) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_119, c_2])).
% 17.85/7.72  tff(c_11399, plain, (![A_446, B_447]: (r2_hidden('#skF_1'(A_446, B_447), k1_xboole_0) | ~r1_tarski(A_446, k1_setfam_1('#skF_10')) | r1_tarski(A_446, B_447))), inference(resolution, [status(thm)], [c_11259, c_129])).
% 17.85/7.72  tff(c_11425, plain, (![A_446]: (~r1_tarski(A_446, k1_setfam_1('#skF_10')) | r1_tarski(A_446, k1_xboole_0))), inference(resolution, [status(thm)], [c_11399, c_4])).
% 17.85/7.72  tff(c_12450, plain, (![A_487, C_489]: (r1_tarski(A_487, k1_xboole_0) | r2_hidden(C_489, k3_tarski('#skF_10')) | ~r2_hidden(C_489, k1_setfam_1('#skF_10')) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_12385, c_11425])).
% 17.85/7.72  tff(c_12474, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_12450])).
% 17.85/7.72  tff(c_11258, plain, (~r1_tarski(k1_xboole_0, '#skF_10')), inference(splitRight, [status(thm)], [c_1569])).
% 17.85/7.72  tff(c_12618, plain, (~r1_tarski('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_12474, c_11258])).
% 17.85/7.72  tff(c_12654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_12618])).
% 17.85/7.72  tff(c_12655, plain, (![C_489, A_487]: (r2_hidden(C_489, k3_tarski('#skF_10')) | ~r2_hidden(C_489, k1_setfam_1('#skF_10')) | r1_tarski(A_487, k1_xboole_0))), inference(splitRight, [status(thm)], [c_12450])).
% 17.85/7.72  tff(c_12657, plain, (![A_487]: (r1_tarski(A_487, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_12655])).
% 17.85/7.72  tff(c_12656, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_12450])).
% 17.85/7.72  tff(c_11688, plain, (![C_462, A_463, C_464]: (r2_hidden(C_462, '#skF_5'(A_463, k3_tarski(A_463), C_464)) | ~r2_hidden(C_462, k1_setfam_1(A_463)) | k1_xboole_0=A_463 | ~r2_hidden(C_464, k3_tarski(A_463)))), inference(resolution, [status(thm)], [c_10, c_131])).
% 17.85/7.72  tff(c_11757, plain, (![C_467, A_468, C_469]: (r2_hidden(C_467, k3_tarski(A_468)) | ~r2_hidden(C_467, k1_setfam_1(A_468)) | k1_xboole_0=A_468 | ~r2_hidden(C_469, k3_tarski(A_468)))), inference(resolution, [status(thm)], [c_11688, c_108])).
% 17.85/7.72  tff(c_11876, plain, (![C_470, A_471, B_472]: (r2_hidden(C_470, k3_tarski(A_471)) | ~r2_hidden(C_470, k1_setfam_1(A_471)) | k1_xboole_0=A_471 | r1_tarski(k3_tarski(A_471), B_472))), inference(resolution, [status(thm)], [c_6, c_11757])).
% 17.85/7.72  tff(c_11964, plain, (![A_473, C_474]: (k3_tarski(A_473)=k1_xboole_0 | r2_hidden(C_474, k3_tarski(A_473)) | ~r2_hidden(C_474, k1_setfam_1(A_473)) | k1_xboole_0=A_473)), inference(resolution, [status(thm)], [c_11876, c_26])).
% 17.85/7.72  tff(c_38314, plain, (![A_980, A_981]: (r1_tarski(A_980, k3_tarski(A_981)) | k3_tarski(A_981)=k1_xboole_0 | ~r2_hidden('#skF_1'(A_980, k3_tarski(A_981)), k1_setfam_1(A_981)) | k1_xboole_0=A_981)), inference(resolution, [status(thm)], [c_11964, c_4])).
% 17.85/7.72  tff(c_38523, plain, (![A_985]: (k3_tarski(A_985)=k1_xboole_0 | k1_xboole_0=A_985 | r1_tarski(k1_setfam_1(A_985), k3_tarski(A_985)))), inference(resolution, [status(thm)], [c_6, c_38314])).
% 17.85/7.72  tff(c_38540, plain, (k3_tarski('#skF_10')=k1_xboole_0 | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_38523, c_54])).
% 17.85/7.72  tff(c_38568, plain, (k3_tarski('#skF_10')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_12656, c_38540])).
% 17.85/7.72  tff(c_38577, plain, (~r1_tarski(k1_setfam_1('#skF_10'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38568, c_54])).
% 17.85/7.72  tff(c_38580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12657, c_38577])).
% 17.85/7.72  tff(c_38582, plain, (![C_986]: (r2_hidden(C_986, k3_tarski('#skF_10')) | ~r2_hidden(C_986, k1_setfam_1('#skF_10')))), inference(splitRight, [status(thm)], [c_12655])).
% 17.85/7.72  tff(c_38771, plain, (![A_992]: (r1_tarski(A_992, k3_tarski('#skF_10')) | ~r2_hidden('#skF_1'(A_992, k3_tarski('#skF_10')), k1_setfam_1('#skF_10')))), inference(resolution, [status(thm)], [c_38582, c_4])).
% 17.85/7.72  tff(c_38786, plain, (r1_tarski(k1_setfam_1('#skF_10'), k3_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_6, c_38771])).
% 17.85/7.72  tff(c_38794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_38786])).
% 17.85/7.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.85/7.72  
% 17.85/7.72  Inference rules
% 17.85/7.72  ----------------------
% 17.85/7.72  #Ref     : 0
% 17.85/7.72  #Sup     : 9368
% 17.85/7.72  #Fact    : 0
% 17.85/7.72  #Define  : 0
% 17.85/7.72  #Split   : 15
% 17.85/7.72  #Chain   : 0
% 17.85/7.72  #Close   : 0
% 17.85/7.72  
% 17.85/7.72  Ordering : KBO
% 17.85/7.72  
% 17.85/7.72  Simplification rules
% 17.85/7.72  ----------------------
% 17.85/7.72  #Subsume      : 2056
% 17.85/7.72  #Demod        : 1416
% 17.85/7.72  #Tautology    : 366
% 17.85/7.72  #SimpNegUnit  : 88
% 17.85/7.72  #BackRed      : 211
% 17.85/7.72  
% 17.85/7.72  #Partial instantiations: 0
% 17.85/7.72  #Strategies tried      : 1
% 17.85/7.72  
% 17.85/7.72  Timing (in seconds)
% 17.85/7.72  ----------------------
% 17.85/7.73  Preprocessing        : 0.28
% 17.85/7.73  Parsing              : 0.14
% 17.85/7.73  CNF conversion       : 0.02
% 17.85/7.73  Main loop            : 6.58
% 17.85/7.73  Inferencing          : 1.14
% 17.85/7.73  Reduction            : 1.00
% 17.85/7.73  Demodulation         : 0.57
% 17.85/7.73  BG Simplification    : 0.19
% 17.85/7.73  Subsumption          : 3.73
% 17.85/7.73  Abstraction          : 0.24
% 17.85/7.73  MUC search           : 0.00
% 17.85/7.73  Cooper               : 0.00
% 17.85/7.73  Total                : 6.94
% 17.85/7.73  Index Insertion      : 0.00
% 17.85/7.73  Index Deletion       : 0.00
% 17.85/7.73  Index Matching       : 0.00
% 17.85/7.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
