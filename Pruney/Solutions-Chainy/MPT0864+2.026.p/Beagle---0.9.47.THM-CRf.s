%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 771 expanded)
%              Number of leaves         :   33 ( 274 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 (1546 expanded)
%              Number of equality atoms :   93 (1179 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_66,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_119,plain,(
    ! [A_70,B_71] : k1_mcart_1(k4_tarski(A_70,B_71)) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,(
    k1_mcart_1('#skF_10') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_119])).

tff(c_94,plain,(
    ! [A_67,B_68] : k2_mcart_1(k4_tarski(A_67,B_68)) = B_68 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    k2_mcart_1('#skF_10') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_94])).

tff(c_64,plain,
    ( k2_mcart_1('#skF_10') = '#skF_10'
    | k1_mcart_1('#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_135,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_103,c_64])).

tff(c_136,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_138,plain,(
    k4_tarski('#skF_10','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_66])).

tff(c_58,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_9'(A_52),A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_160,plain,(
    ! [C_73,A_74] :
      ( C_73 = A_74
      | ~ r2_hidden(C_73,k1_tarski(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,(
    ! [A_74] :
      ( '#skF_9'(k1_tarski(A_74)) = A_74
      | k1_tarski(A_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_160])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_246,plain,(
    ! [D_93,A_94,C_95] :
      ( ~ r2_hidden(D_93,A_94)
      | k4_tarski(C_95,D_93) != '#skF_9'(A_94)
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_258,plain,(
    ! [C_100,C_101] :
      ( k4_tarski(C_100,C_101) != '#skF_9'(k1_tarski(C_101))
      | k1_tarski(C_101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_246])).

tff(c_371,plain,(
    ! [C_109,A_110] :
      ( k4_tarski(C_109,A_110) != A_110
      | k1_tarski(A_110) = k1_xboole_0
      | k1_tarski(A_110) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_258])).

tff(c_374,plain,
    ( '#skF_10' != '#skF_12'
    | k1_tarski('#skF_12') = k1_xboole_0
    | k1_tarski('#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_371])).

tff(c_375,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_231,plain,(
    ! [C_86,A_87,D_88] :
      ( ~ r2_hidden(C_86,A_87)
      | k4_tarski(C_86,D_88) != '#skF_9'(A_87)
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_242,plain,(
    ! [C_91,D_92] :
      ( k4_tarski(C_91,D_92) != '#skF_9'(k1_tarski(C_91))
      | k1_tarski(C_91) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_231])).

tff(c_262,plain,(
    ! [A_102,D_103] :
      ( k4_tarski(A_102,D_103) != A_102
      | k1_tarski(A_102) = k1_xboole_0
      | k1_tarski(A_102) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_242])).

tff(c_266,plain,(
    k1_tarski('#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_262])).

tff(c_294,plain,(
    r2_hidden('#skF_10',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_4])).

tff(c_46,plain,(
    ! [A_46] : k2_zfmisc_1(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_490,plain,(
    ! [E_119,F_120,A_121,B_122] :
      ( r2_hidden(k4_tarski(E_119,F_120),k2_zfmisc_1(A_121,B_122))
      | ~ r2_hidden(F_120,B_122)
      | ~ r2_hidden(E_119,A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_522,plain,(
    ! [E_125,F_126,A_127] :
      ( r2_hidden(k4_tarski(E_125,F_126),k1_xboole_0)
      | ~ r2_hidden(F_126,k1_xboole_0)
      | ~ r2_hidden(E_125,A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_490])).

tff(c_547,plain,(
    ! [C_128,F_129] :
      ( r2_hidden(k4_tarski(C_128,F_129),k1_xboole_0)
      | ~ r2_hidden(F_129,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_522])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_291,plain,(
    ! [C_5] :
      ( C_5 = '#skF_10'
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_2])).

tff(c_564,plain,(
    ! [C_130,F_131] :
      ( k4_tarski(C_130,F_131) = '#skF_10'
      | ~ r2_hidden(F_131,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_547,c_291])).

tff(c_587,plain,(
    ! [C_132] : k4_tarski(C_132,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_294,c_564])).

tff(c_56,plain,(
    ! [A_50,B_51] : k2_mcart_1(k4_tarski(A_50,B_51)) = B_51 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_613,plain,(
    k2_mcart_1('#skF_10') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_56])).

tff(c_622,plain,(
    '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_613])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_622])).

tff(c_626,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_630,plain,(
    r2_hidden('#skF_12',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_294])).

tff(c_48,plain,(
    ! [B_47] : k2_zfmisc_1(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_721,plain,(
    ! [E_135,F_136,A_137,B_138] :
      ( r2_hidden(k4_tarski(E_135,F_136),k2_zfmisc_1(A_137,B_138))
      | ~ r2_hidden(F_136,B_138)
      | ~ r2_hidden(E_135,A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_802,plain,(
    ! [E_144,F_145,B_146] :
      ( r2_hidden(k4_tarski(E_144,F_145),k1_xboole_0)
      | ~ r2_hidden(F_145,B_146)
      | ~ r2_hidden(E_144,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_721])).

tff(c_841,plain,(
    ! [E_149,C_150] :
      ( r2_hidden(k4_tarski(E_149,C_150),k1_xboole_0)
      | ~ r2_hidden(E_149,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_802])).

tff(c_629,plain,(
    ! [C_5] :
      ( C_5 = '#skF_12'
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_291])).

tff(c_859,plain,(
    ! [E_151,C_152] :
      ( k4_tarski(E_151,C_152) = '#skF_12'
      | ~ r2_hidden(E_151,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_841,c_629])).

tff(c_880,plain,(
    ! [C_153] : k4_tarski('#skF_12',C_153) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_630,c_859])).

tff(c_1131,plain,(
    k2_mcart_1('#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_56])).

tff(c_970,plain,(
    ! [C_155] : k2_mcart_1('#skF_12') = C_155 ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_56])).

tff(c_1447,plain,(
    ! [C_5888] : k1_xboole_0 = C_5888 ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_970])).

tff(c_50,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_288,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),k1_xboole_0) != k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_50])).

tff(c_302,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_266,c_288])).

tff(c_1561,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_302])).

tff(c_1562,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_1563,plain,(
    '#skF_11' != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_1572,plain,(
    '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1563])).

tff(c_1566,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_66])).

tff(c_1593,plain,(
    ! [C_7223,A_7224] :
      ( C_7223 = A_7224
      | ~ r2_hidden(C_7223,k1_tarski(A_7224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1601,plain,(
    ! [A_7224] :
      ( '#skF_9'(k1_tarski(A_7224)) = A_7224
      | k1_tarski(A_7224) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_1593])).

tff(c_1675,plain,(
    ! [D_7241,A_7242,C_7243] :
      ( ~ r2_hidden(D_7241,A_7242)
      | k4_tarski(C_7243,D_7241) != '#skF_9'(A_7242)
      | k1_xboole_0 = A_7242 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1690,plain,(
    ! [C_7248,C_7249] :
      ( k4_tarski(C_7248,C_7249) != '#skF_9'(k1_tarski(C_7249))
      | k1_tarski(C_7249) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1675])).

tff(c_1698,plain,(
    ! [C_7252,A_7253] :
      ( k4_tarski(C_7252,A_7253) != A_7253
      | k1_tarski(A_7253) = k1_xboole_0
      | k1_tarski(A_7253) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_1690])).

tff(c_1702,plain,(
    k1_tarski('#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_1698])).

tff(c_1731,plain,(
    r2_hidden('#skF_12',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_4])).

tff(c_1809,plain,(
    ! [E_7263,F_7264,A_7265,B_7266] :
      ( r2_hidden(k4_tarski(E_7263,F_7264),k2_zfmisc_1(A_7265,B_7266))
      | ~ r2_hidden(F_7264,B_7266)
      | ~ r2_hidden(E_7263,A_7265) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1825,plain,(
    ! [E_7267,F_7268,A_7269] :
      ( r2_hidden(k4_tarski(E_7267,F_7268),k1_xboole_0)
      | ~ r2_hidden(F_7268,k1_xboole_0)
      | ~ r2_hidden(E_7267,A_7269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1809])).

tff(c_1841,plain,(
    ! [C_7270,F_7271] :
      ( r2_hidden(k4_tarski(C_7270,F_7271),k1_xboole_0)
      | ~ r2_hidden(F_7271,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_1825])).

tff(c_1728,plain,(
    ! [C_5] :
      ( C_5 = '#skF_12'
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_2])).

tff(c_1859,plain,(
    ! [C_7272,F_7273] :
      ( k4_tarski(C_7272,F_7273) = '#skF_12'
      | ~ r2_hidden(F_7273,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1841,c_1728])).

tff(c_1892,plain,(
    ! [C_7276] : k4_tarski(C_7276,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1731,c_1859])).

tff(c_54,plain,(
    ! [A_50,B_51] : k1_mcart_1(k4_tarski(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1939,plain,(
    k1_mcart_1('#skF_12') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_54])).

tff(c_1915,plain,(
    ! [C_7276] : k1_mcart_1('#skF_12') = C_7276 ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_54])).

tff(c_2124,plain,(
    ! [C_9041] : C_9041 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_1939,c_1915])).

tff(c_1872,plain,(
    ! [C_7272] : k4_tarski(C_7272,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1731,c_1859])).

tff(c_2134,plain,(
    '#skF_11' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_2124,c_1872])).

tff(c_2257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1572,c_2134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  
% 3.77/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 3.77/1.64  
% 3.77/1.64  %Foreground sorts:
% 3.77/1.64  
% 3.77/1.64  
% 3.77/1.64  %Background operators:
% 3.77/1.64  
% 3.77/1.64  
% 3.77/1.64  %Foreground operators:
% 3.77/1.64  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.64  tff('#skF_11', type, '#skF_11': $i).
% 3.77/1.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.77/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.77/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.77/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.77/1.64  tff('#skF_10', type, '#skF_10': $i).
% 3.77/1.64  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.77/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.77/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.77/1.64  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.64  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.77/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.77/1.64  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.77/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.77/1.64  tff('#skF_12', type, '#skF_12': $i).
% 3.77/1.64  
% 3.77/1.66  tff(f_91, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.77/1.66  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.77/1.66  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.77/1.66  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.77/1.66  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.77/1.66  tff(f_50, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.77/1.66  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.77/1.66  tff(c_66, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/1.66  tff(c_119, plain, (![A_70, B_71]: (k1_mcart_1(k4_tarski(A_70, B_71))=A_70)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.77/1.66  tff(c_128, plain, (k1_mcart_1('#skF_10')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_66, c_119])).
% 3.77/1.66  tff(c_94, plain, (![A_67, B_68]: (k2_mcart_1(k4_tarski(A_67, B_68))=B_68)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.77/1.66  tff(c_103, plain, (k2_mcart_1('#skF_10')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_66, c_94])).
% 3.77/1.66  tff(c_64, plain, (k2_mcart_1('#skF_10')='#skF_10' | k1_mcart_1('#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/1.66  tff(c_135, plain, ('#skF_10'='#skF_12' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_103, c_64])).
% 3.77/1.66  tff(c_136, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_135])).
% 3.77/1.66  tff(c_138, plain, (k4_tarski('#skF_10', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_66])).
% 3.77/1.66  tff(c_58, plain, (![A_52]: (r2_hidden('#skF_9'(A_52), A_52) | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.77/1.66  tff(c_160, plain, (![C_73, A_74]: (C_73=A_74 | ~r2_hidden(C_73, k1_tarski(A_74)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.66  tff(c_168, plain, (![A_74]: ('#skF_9'(k1_tarski(A_74))=A_74 | k1_tarski(A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_160])).
% 3.77/1.66  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.66  tff(c_246, plain, (![D_93, A_94, C_95]: (~r2_hidden(D_93, A_94) | k4_tarski(C_95, D_93)!='#skF_9'(A_94) | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.77/1.66  tff(c_258, plain, (![C_100, C_101]: (k4_tarski(C_100, C_101)!='#skF_9'(k1_tarski(C_101)) | k1_tarski(C_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_246])).
% 3.77/1.66  tff(c_371, plain, (![C_109, A_110]: (k4_tarski(C_109, A_110)!=A_110 | k1_tarski(A_110)=k1_xboole_0 | k1_tarski(A_110)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_258])).
% 3.77/1.66  tff(c_374, plain, ('#skF_10'!='#skF_12' | k1_tarski('#skF_12')=k1_xboole_0 | k1_tarski('#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_138, c_371])).
% 3.77/1.66  tff(c_375, plain, ('#skF_10'!='#skF_12'), inference(splitLeft, [status(thm)], [c_374])).
% 3.77/1.66  tff(c_231, plain, (![C_86, A_87, D_88]: (~r2_hidden(C_86, A_87) | k4_tarski(C_86, D_88)!='#skF_9'(A_87) | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.77/1.66  tff(c_242, plain, (![C_91, D_92]: (k4_tarski(C_91, D_92)!='#skF_9'(k1_tarski(C_91)) | k1_tarski(C_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_231])).
% 3.77/1.66  tff(c_262, plain, (![A_102, D_103]: (k4_tarski(A_102, D_103)!=A_102 | k1_tarski(A_102)=k1_xboole_0 | k1_tarski(A_102)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_242])).
% 3.77/1.66  tff(c_266, plain, (k1_tarski('#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_138, c_262])).
% 3.77/1.66  tff(c_294, plain, (r2_hidden('#skF_10', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_4])).
% 3.77/1.66  tff(c_46, plain, (![A_46]: (k2_zfmisc_1(A_46, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.77/1.66  tff(c_490, plain, (![E_119, F_120, A_121, B_122]: (r2_hidden(k4_tarski(E_119, F_120), k2_zfmisc_1(A_121, B_122)) | ~r2_hidden(F_120, B_122) | ~r2_hidden(E_119, A_121))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.66  tff(c_522, plain, (![E_125, F_126, A_127]: (r2_hidden(k4_tarski(E_125, F_126), k1_xboole_0) | ~r2_hidden(F_126, k1_xboole_0) | ~r2_hidden(E_125, A_127))), inference(superposition, [status(thm), theory('equality')], [c_46, c_490])).
% 3.77/1.66  tff(c_547, plain, (![C_128, F_129]: (r2_hidden(k4_tarski(C_128, F_129), k1_xboole_0) | ~r2_hidden(F_129, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_522])).
% 3.77/1.66  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.66  tff(c_291, plain, (![C_5]: (C_5='#skF_10' | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_266, c_2])).
% 3.77/1.66  tff(c_564, plain, (![C_130, F_131]: (k4_tarski(C_130, F_131)='#skF_10' | ~r2_hidden(F_131, k1_xboole_0))), inference(resolution, [status(thm)], [c_547, c_291])).
% 3.77/1.66  tff(c_587, plain, (![C_132]: (k4_tarski(C_132, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_294, c_564])).
% 3.77/1.66  tff(c_56, plain, (![A_50, B_51]: (k2_mcart_1(k4_tarski(A_50, B_51))=B_51)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.77/1.66  tff(c_613, plain, (k2_mcart_1('#skF_10')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_587, c_56])).
% 3.77/1.66  tff(c_622, plain, ('#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_613])).
% 3.77/1.66  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_622])).
% 3.77/1.66  tff(c_626, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_374])).
% 3.77/1.66  tff(c_630, plain, (r2_hidden('#skF_12', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_626, c_294])).
% 3.77/1.66  tff(c_48, plain, (![B_47]: (k2_zfmisc_1(k1_xboole_0, B_47)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.77/1.66  tff(c_721, plain, (![E_135, F_136, A_137, B_138]: (r2_hidden(k4_tarski(E_135, F_136), k2_zfmisc_1(A_137, B_138)) | ~r2_hidden(F_136, B_138) | ~r2_hidden(E_135, A_137))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.66  tff(c_802, plain, (![E_144, F_145, B_146]: (r2_hidden(k4_tarski(E_144, F_145), k1_xboole_0) | ~r2_hidden(F_145, B_146) | ~r2_hidden(E_144, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_721])).
% 3.77/1.66  tff(c_841, plain, (![E_149, C_150]: (r2_hidden(k4_tarski(E_149, C_150), k1_xboole_0) | ~r2_hidden(E_149, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_802])).
% 3.77/1.66  tff(c_629, plain, (![C_5]: (C_5='#skF_12' | ~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_626, c_291])).
% 3.77/1.66  tff(c_859, plain, (![E_151, C_152]: (k4_tarski(E_151, C_152)='#skF_12' | ~r2_hidden(E_151, k1_xboole_0))), inference(resolution, [status(thm)], [c_841, c_629])).
% 3.77/1.66  tff(c_880, plain, (![C_153]: (k4_tarski('#skF_12', C_153)='#skF_12')), inference(resolution, [status(thm)], [c_630, c_859])).
% 3.77/1.66  tff(c_1131, plain, (k2_mcart_1('#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_880, c_56])).
% 3.77/1.66  tff(c_970, plain, (![C_155]: (k2_mcart_1('#skF_12')=C_155)), inference(superposition, [status(thm), theory('equality')], [c_880, c_56])).
% 3.77/1.66  tff(c_1447, plain, (![C_5888]: (k1_xboole_0=C_5888)), inference(superposition, [status(thm), theory('equality')], [c_1131, c_970])).
% 3.77/1.66  tff(c_50, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.77/1.66  tff(c_288, plain, (k4_xboole_0(k1_tarski('#skF_10'), k1_xboole_0)!=k1_tarski('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_266, c_50])).
% 3.77/1.66  tff(c_302, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_266, c_266, c_288])).
% 3.77/1.66  tff(c_1561, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1447, c_302])).
% 3.77/1.66  tff(c_1562, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_135])).
% 3.77/1.66  tff(c_1563, plain, ('#skF_11'!='#skF_10'), inference(splitRight, [status(thm)], [c_135])).
% 3.77/1.66  tff(c_1572, plain, ('#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_1563])).
% 3.77/1.66  tff(c_1566, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_66])).
% 3.77/1.66  tff(c_1593, plain, (![C_7223, A_7224]: (C_7223=A_7224 | ~r2_hidden(C_7223, k1_tarski(A_7224)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.77/1.66  tff(c_1601, plain, (![A_7224]: ('#skF_9'(k1_tarski(A_7224))=A_7224 | k1_tarski(A_7224)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_1593])).
% 3.77/1.66  tff(c_1675, plain, (![D_7241, A_7242, C_7243]: (~r2_hidden(D_7241, A_7242) | k4_tarski(C_7243, D_7241)!='#skF_9'(A_7242) | k1_xboole_0=A_7242)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.77/1.66  tff(c_1690, plain, (![C_7248, C_7249]: (k4_tarski(C_7248, C_7249)!='#skF_9'(k1_tarski(C_7249)) | k1_tarski(C_7249)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1675])).
% 3.77/1.66  tff(c_1698, plain, (![C_7252, A_7253]: (k4_tarski(C_7252, A_7253)!=A_7253 | k1_tarski(A_7253)=k1_xboole_0 | k1_tarski(A_7253)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1601, c_1690])).
% 3.77/1.66  tff(c_1702, plain, (k1_tarski('#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1566, c_1698])).
% 3.77/1.66  tff(c_1731, plain, (r2_hidden('#skF_12', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1702, c_4])).
% 3.77/1.66  tff(c_1809, plain, (![E_7263, F_7264, A_7265, B_7266]: (r2_hidden(k4_tarski(E_7263, F_7264), k2_zfmisc_1(A_7265, B_7266)) | ~r2_hidden(F_7264, B_7266) | ~r2_hidden(E_7263, A_7265))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.77/1.66  tff(c_1825, plain, (![E_7267, F_7268, A_7269]: (r2_hidden(k4_tarski(E_7267, F_7268), k1_xboole_0) | ~r2_hidden(F_7268, k1_xboole_0) | ~r2_hidden(E_7267, A_7269))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1809])).
% 3.77/1.66  tff(c_1841, plain, (![C_7270, F_7271]: (r2_hidden(k4_tarski(C_7270, F_7271), k1_xboole_0) | ~r2_hidden(F_7271, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_1825])).
% 3.77/1.66  tff(c_1728, plain, (![C_5]: (C_5='#skF_12' | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1702, c_2])).
% 3.77/1.66  tff(c_1859, plain, (![C_7272, F_7273]: (k4_tarski(C_7272, F_7273)='#skF_12' | ~r2_hidden(F_7273, k1_xboole_0))), inference(resolution, [status(thm)], [c_1841, c_1728])).
% 3.77/1.66  tff(c_1892, plain, (![C_7276]: (k4_tarski(C_7276, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1731, c_1859])).
% 3.77/1.66  tff(c_54, plain, (![A_50, B_51]: (k1_mcart_1(k4_tarski(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.77/1.66  tff(c_1939, plain, (k1_mcart_1('#skF_12')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_1892, c_54])).
% 3.77/1.66  tff(c_1915, plain, (![C_7276]: (k1_mcart_1('#skF_12')=C_7276)), inference(superposition, [status(thm), theory('equality')], [c_1892, c_54])).
% 3.77/1.66  tff(c_2124, plain, (![C_9041]: (C_9041='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1939, c_1915])).
% 3.77/1.66  tff(c_1872, plain, (![C_7272]: (k4_tarski(C_7272, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1731, c_1859])).
% 3.77/1.66  tff(c_2134, plain, ('#skF_11'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_2124, c_1872])).
% 3.77/1.66  tff(c_2257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1572, c_2134])).
% 3.77/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.66  
% 3.77/1.66  Inference rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Ref     : 0
% 3.77/1.66  #Sup     : 724
% 3.77/1.66  #Fact    : 0
% 3.77/1.66  #Define  : 0
% 3.77/1.66  #Split   : 2
% 3.77/1.66  #Chain   : 0
% 3.77/1.66  #Close   : 0
% 3.77/1.66  
% 3.77/1.66  Ordering : KBO
% 3.77/1.66  
% 3.77/1.66  Simplification rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Subsume      : 112
% 3.77/1.66  #Demod        : 98
% 3.77/1.66  #Tautology    : 175
% 3.77/1.66  #SimpNegUnit  : 10
% 3.77/1.66  #BackRed      : 14
% 3.77/1.66  
% 3.77/1.66  #Partial instantiations: 1625
% 3.77/1.66  #Strategies tried      : 1
% 3.77/1.66  
% 3.77/1.66  Timing (in seconds)
% 3.77/1.66  ----------------------
% 3.77/1.66  Preprocessing        : 0.33
% 3.77/1.66  Parsing              : 0.16
% 3.77/1.66  CNF conversion       : 0.03
% 3.77/1.66  Main loop            : 0.56
% 3.77/1.66  Inferencing          : 0.25
% 3.77/1.66  Reduction            : 0.14
% 3.77/1.66  Demodulation         : 0.10
% 3.77/1.66  BG Simplification    : 0.03
% 3.77/1.66  Subsumption          : 0.09
% 3.77/1.66  Abstraction          : 0.03
% 3.77/1.66  MUC search           : 0.00
% 3.77/1.66  Cooper               : 0.00
% 3.77/1.66  Total                : 0.93
% 3.77/1.66  Index Insertion      : 0.00
% 3.77/1.66  Index Deletion       : 0.00
% 3.77/1.66  Index Matching       : 0.00
% 3.77/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
