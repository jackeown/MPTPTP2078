%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 311 expanded)
%              Number of leaves         :   39 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  170 ( 757 expanded)
%              Number of equality atoms :   75 ( 415 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_13 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_89,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2130,plain,(
    ! [A_241,B_242] :
      ( r2_hidden(k4_tarski('#skF_8'(A_241,B_242),'#skF_7'(A_241,B_242)),A_241)
      | r2_hidden('#skF_9'(A_241,B_242),B_242)
      | k2_relat_1(A_241) = B_242 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,(
    ! [A_72,B_73] : ~ r2_hidden(A_72,k2_zfmisc_1(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_131])).

tff(c_2163,plain,(
    ! [B_242] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_242),B_242)
      | k2_relat_1(k1_xboole_0) = B_242 ) ),
    inference(resolution,[status(thm)],[c_2130,c_134])).

tff(c_2174,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_243),B_243)
      | k1_xboole_0 = B_243 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2163])).

tff(c_58,plain,(
    ! [A_54,B_58] :
      ( k1_relat_1('#skF_11'(A_54,B_58)) = A_54
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [A_54,B_58] :
      ( v1_funct_1('#skF_11'(A_54,B_58))
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,(
    ! [A_54,B_58] :
      ( v1_relat_1('#skF_11'(A_54,B_58))
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_182,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_289,plain,(
    ! [A_114,B_115] :
      ( '#skF_1'(k1_tarski(A_114),B_115) = A_114
      | r1_tarski(k1_tarski(A_114),B_115) ) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_195,plain,(
    ! [A_92,B_93] :
      ( k2_relat_1('#skF_11'(A_92,B_93)) = k1_tarski(B_93)
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    ! [C_61] :
      ( ~ r1_tarski(k2_relat_1(C_61),'#skF_12')
      | k1_relat_1(C_61) != '#skF_13'
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_201,plain,(
    ! [B_93,A_92] :
      ( ~ r1_tarski(k1_tarski(B_93),'#skF_12')
      | k1_relat_1('#skF_11'(A_92,B_93)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_92,B_93))
      | ~ v1_relat_1('#skF_11'(A_92,B_93))
      | k1_xboole_0 = A_92 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_64])).

tff(c_359,plain,(
    ! [A_129,A_130] :
      ( k1_relat_1('#skF_11'(A_129,A_130)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_129,A_130))
      | ~ v1_relat_1('#skF_11'(A_129,A_130))
      | k1_xboole_0 = A_129
      | '#skF_1'(k1_tarski(A_130),'#skF_12') = A_130 ) ),
    inference(resolution,[status(thm)],[c_289,c_201])).

tff(c_661,plain,(
    ! [A_155,B_156] :
      ( k1_relat_1('#skF_11'(A_155,B_156)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_155,B_156))
      | '#skF_1'(k1_tarski(B_156),'#skF_12') = B_156
      | k1_xboole_0 = A_155 ) ),
    inference(resolution,[status(thm)],[c_62,c_359])).

tff(c_753,plain,(
    ! [A_164,B_165] :
      ( k1_relat_1('#skF_11'(A_164,B_165)) != '#skF_13'
      | '#skF_1'(k1_tarski(B_165),'#skF_12') = B_165
      | k1_xboole_0 = A_164 ) ),
    inference(resolution,[status(thm)],[c_60,c_661])).

tff(c_756,plain,(
    ! [A_54,B_58] :
      ( A_54 != '#skF_13'
      | '#skF_1'(k1_tarski(B_58),'#skF_12') = B_58
      | k1_xboole_0 = A_54
      | k1_xboole_0 = A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_753])).

tff(c_943,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_63] :
      ( v1_funct_1(A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_81,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [C_65] :
      ( ~ r1_tarski(k2_relat_1(C_65),'#skF_12')
      | k1_relat_1(C_65) != '#skF_13'
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_86,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_12')
    | k1_relat_1(k1_xboole_0) != '#skF_13'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_83])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_13'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_52,c_10,c_86])).

tff(c_111,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_36,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,(
    ! [A_68,B_69] : ~ r2_hidden(A_68,k2_zfmisc_1(A_68,B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_112])).

tff(c_124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_124])).

tff(c_129,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_129])).

tff(c_972,plain,(
    ! [B_183] : '#skF_1'(k1_tarski(B_183),'#skF_12') = B_183 ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1006,plain,(
    ! [B_184] :
      ( ~ r2_hidden(B_184,'#skF_12')
      | r1_tarski(k1_tarski(B_184),'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_4])).

tff(c_1021,plain,(
    ! [A_185,B_186] :
      ( k1_relat_1('#skF_11'(A_185,B_186)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_185,B_186))
      | ~ v1_relat_1('#skF_11'(A_185,B_186))
      | k1_xboole_0 = A_185
      | ~ r2_hidden(B_186,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_1006,c_201])).

tff(c_1315,plain,(
    ! [A_210,B_211] :
      ( k1_relat_1('#skF_11'(A_210,B_211)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_210,B_211))
      | ~ r2_hidden(B_211,'#skF_12')
      | k1_xboole_0 = A_210 ) ),
    inference(resolution,[status(thm)],[c_62,c_1021])).

tff(c_1332,plain,(
    ! [A_214,B_215] :
      ( k1_relat_1('#skF_11'(A_214,B_215)) != '#skF_13'
      | ~ r2_hidden(B_215,'#skF_12')
      | k1_xboole_0 = A_214 ) ),
    inference(resolution,[status(thm)],[c_60,c_1315])).

tff(c_1335,plain,(
    ! [A_54,B_58] :
      ( A_54 != '#skF_13'
      | ~ r2_hidden(B_58,'#skF_12')
      | k1_xboole_0 = A_54
      | k1_xboole_0 = A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1332])).

tff(c_1336,plain,(
    ! [B_58] : ~ r2_hidden(B_58,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_1335])).

tff(c_2194,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2174,c_1336])).

tff(c_2212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2194])).

tff(c_2214,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_1335])).

tff(c_2240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_129])).

tff(c_2242,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2241,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2252,plain,(
    '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2242,c_2241])).

tff(c_2246,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_8])).

tff(c_2257,plain,(
    v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_2246])).

tff(c_2306,plain,(
    ! [A_250] :
      ( v1_funct_1(A_250)
      | ~ v1_xboole_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2310,plain,(
    v1_funct_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_2257,c_2306])).

tff(c_2244,plain,(
    k1_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_2241,c_52])).

tff(c_2263,plain,(
    k1_relat_1('#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_2252,c_2244])).

tff(c_2243,plain,(
    ! [A_6] : r1_tarski('#skF_13',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_10])).

tff(c_2268,plain,(
    ! [A_6] : r1_tarski('#skF_12',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_2243])).

tff(c_2245,plain,(
    k2_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_2241,c_50])).

tff(c_2270,plain,(
    k2_relat_1('#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_2252,c_2245])).

tff(c_2284,plain,(
    ! [C_248] :
      ( ~ r1_tarski(k2_relat_1(C_248),'#skF_12')
      | k1_relat_1(C_248) != '#skF_12'
      | ~ v1_funct_1(C_248)
      | ~ v1_relat_1(C_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_64])).

tff(c_2287,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | k1_relat_1('#skF_12') != '#skF_12'
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2270,c_2284])).

tff(c_2289,plain,
    ( ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2263,c_2268,c_2287])).

tff(c_2312,plain,(
    ~ v1_relat_1('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2289])).

tff(c_2331,plain,(
    ! [A_260] :
      ( r2_hidden('#skF_4'(A_260),A_260)
      | v1_relat_1(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2290,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2242,c_2242,c_26])).

tff(c_2313,plain,(
    ! [A_251,B_252] : ~ r2_hidden(A_251,k2_zfmisc_1(A_251,B_252)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2316,plain,(
    ! [A_12] : ~ r2_hidden(A_12,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2290,c_2313])).

tff(c_2335,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_2331,c_2316])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2312,c_2335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.59  
% 3.78/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.59  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_13 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_10
% 3.78/1.59  
% 3.78/1.59  %Foreground sorts:
% 3.78/1.59  
% 3.78/1.59  
% 3.78/1.59  %Background operators:
% 3.78/1.59  
% 3.78/1.59  
% 3.78/1.59  %Foreground operators:
% 3.78/1.59  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 3.78/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.78/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.78/1.59  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.78/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.78/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.78/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.78/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.78/1.59  tff('#skF_13', type, '#skF_13': $i).
% 3.78/1.59  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.78/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.78/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.78/1.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.78/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.78/1.59  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.78/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.78/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.78/1.59  tff('#skF_12', type, '#skF_12': $i).
% 3.78/1.59  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.78/1.59  
% 3.78/1.61  tff(f_107, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 3.78/1.61  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.78/1.61  tff(f_69, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.78/1.61  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.78/1.61  tff(f_51, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.78/1.61  tff(f_89, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 3.78/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.78/1.61  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.78/1.61  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.78/1.61  tff(f_76, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 3.78/1.61  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.78/1.61  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.78/1.61  tff(c_66, plain, (k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.78/1.61  tff(c_76, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_66])).
% 3.78/1.61  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.78/1.61  tff(c_2130, plain, (![A_241, B_242]: (r2_hidden(k4_tarski('#skF_8'(A_241, B_242), '#skF_7'(A_241, B_242)), A_241) | r2_hidden('#skF_9'(A_241, B_242), B_242) | k2_relat_1(A_241)=B_242)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.78/1.61  tff(c_26, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.78/1.61  tff(c_131, plain, (![A_72, B_73]: (~r2_hidden(A_72, k2_zfmisc_1(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.61  tff(c_134, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_131])).
% 3.78/1.61  tff(c_2163, plain, (![B_242]: (r2_hidden('#skF_9'(k1_xboole_0, B_242), B_242) | k2_relat_1(k1_xboole_0)=B_242)), inference(resolution, [status(thm)], [c_2130, c_134])).
% 3.78/1.61  tff(c_2174, plain, (![B_243]: (r2_hidden('#skF_9'(k1_xboole_0, B_243), B_243) | k1_xboole_0=B_243)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2163])).
% 3.78/1.61  tff(c_58, plain, (![A_54, B_58]: (k1_relat_1('#skF_11'(A_54, B_58))=A_54 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.78/1.61  tff(c_60, plain, (![A_54, B_58]: (v1_funct_1('#skF_11'(A_54, B_58)) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.78/1.61  tff(c_62, plain, (![A_54, B_58]: (v1_relat_1('#skF_11'(A_54, B_58)) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.78/1.61  tff(c_182, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.61  tff(c_12, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.78/1.61  tff(c_289, plain, (![A_114, B_115]: ('#skF_1'(k1_tarski(A_114), B_115)=A_114 | r1_tarski(k1_tarski(A_114), B_115))), inference(resolution, [status(thm)], [c_182, c_12])).
% 3.78/1.61  tff(c_195, plain, (![A_92, B_93]: (k2_relat_1('#skF_11'(A_92, B_93))=k1_tarski(B_93) | k1_xboole_0=A_92)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.78/1.61  tff(c_64, plain, (![C_61]: (~r1_tarski(k2_relat_1(C_61), '#skF_12') | k1_relat_1(C_61)!='#skF_13' | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.78/1.61  tff(c_201, plain, (![B_93, A_92]: (~r1_tarski(k1_tarski(B_93), '#skF_12') | k1_relat_1('#skF_11'(A_92, B_93))!='#skF_13' | ~v1_funct_1('#skF_11'(A_92, B_93)) | ~v1_relat_1('#skF_11'(A_92, B_93)) | k1_xboole_0=A_92)), inference(superposition, [status(thm), theory('equality')], [c_195, c_64])).
% 3.78/1.61  tff(c_359, plain, (![A_129, A_130]: (k1_relat_1('#skF_11'(A_129, A_130))!='#skF_13' | ~v1_funct_1('#skF_11'(A_129, A_130)) | ~v1_relat_1('#skF_11'(A_129, A_130)) | k1_xboole_0=A_129 | '#skF_1'(k1_tarski(A_130), '#skF_12')=A_130)), inference(resolution, [status(thm)], [c_289, c_201])).
% 3.78/1.61  tff(c_661, plain, (![A_155, B_156]: (k1_relat_1('#skF_11'(A_155, B_156))!='#skF_13' | ~v1_funct_1('#skF_11'(A_155, B_156)) | '#skF_1'(k1_tarski(B_156), '#skF_12')=B_156 | k1_xboole_0=A_155)), inference(resolution, [status(thm)], [c_62, c_359])).
% 3.78/1.61  tff(c_753, plain, (![A_164, B_165]: (k1_relat_1('#skF_11'(A_164, B_165))!='#skF_13' | '#skF_1'(k1_tarski(B_165), '#skF_12')=B_165 | k1_xboole_0=A_164)), inference(resolution, [status(thm)], [c_60, c_661])).
% 3.78/1.61  tff(c_756, plain, (![A_54, B_58]: (A_54!='#skF_13' | '#skF_1'(k1_tarski(B_58), '#skF_12')=B_58 | k1_xboole_0=A_54 | k1_xboole_0=A_54)), inference(superposition, [status(thm), theory('equality')], [c_58, c_753])).
% 3.78/1.61  tff(c_943, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_756])).
% 3.78/1.61  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.78/1.61  tff(c_77, plain, (![A_63]: (v1_funct_1(A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.78/1.61  tff(c_81, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_77])).
% 3.78/1.61  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.78/1.61  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.61  tff(c_83, plain, (![C_65]: (~r1_tarski(k2_relat_1(C_65), '#skF_12') | k1_relat_1(C_65)!='#skF_13' | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.78/1.61  tff(c_86, plain, (~r1_tarski(k1_xboole_0, '#skF_12') | k1_relat_1(k1_xboole_0)!='#skF_13' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_83])).
% 3.78/1.61  tff(c_88, plain, (k1_xboole_0!='#skF_13' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_52, c_10, c_86])).
% 3.78/1.61  tff(c_111, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_88])).
% 3.78/1.61  tff(c_36, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.78/1.61  tff(c_112, plain, (![A_68, B_69]: (~r2_hidden(A_68, k2_zfmisc_1(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.61  tff(c_120, plain, (![A_71]: (~r2_hidden(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_112])).
% 3.78/1.61  tff(c_124, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_120])).
% 3.78/1.61  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_124])).
% 3.78/1.61  tff(c_129, plain, (k1_xboole_0!='#skF_13'), inference(splitRight, [status(thm)], [c_88])).
% 3.78/1.61  tff(c_969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_943, c_129])).
% 3.78/1.61  tff(c_972, plain, (![B_183]: ('#skF_1'(k1_tarski(B_183), '#skF_12')=B_183)), inference(splitRight, [status(thm)], [c_756])).
% 3.78/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.61  tff(c_1006, plain, (![B_184]: (~r2_hidden(B_184, '#skF_12') | r1_tarski(k1_tarski(B_184), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_972, c_4])).
% 3.78/1.61  tff(c_1021, plain, (![A_185, B_186]: (k1_relat_1('#skF_11'(A_185, B_186))!='#skF_13' | ~v1_funct_1('#skF_11'(A_185, B_186)) | ~v1_relat_1('#skF_11'(A_185, B_186)) | k1_xboole_0=A_185 | ~r2_hidden(B_186, '#skF_12'))), inference(resolution, [status(thm)], [c_1006, c_201])).
% 3.78/1.61  tff(c_1315, plain, (![A_210, B_211]: (k1_relat_1('#skF_11'(A_210, B_211))!='#skF_13' | ~v1_funct_1('#skF_11'(A_210, B_211)) | ~r2_hidden(B_211, '#skF_12') | k1_xboole_0=A_210)), inference(resolution, [status(thm)], [c_62, c_1021])).
% 3.78/1.61  tff(c_1332, plain, (![A_214, B_215]: (k1_relat_1('#skF_11'(A_214, B_215))!='#skF_13' | ~r2_hidden(B_215, '#skF_12') | k1_xboole_0=A_214)), inference(resolution, [status(thm)], [c_60, c_1315])).
% 3.78/1.61  tff(c_1335, plain, (![A_54, B_58]: (A_54!='#skF_13' | ~r2_hidden(B_58, '#skF_12') | k1_xboole_0=A_54 | k1_xboole_0=A_54)), inference(superposition, [status(thm), theory('equality')], [c_58, c_1332])).
% 3.78/1.61  tff(c_1336, plain, (![B_58]: (~r2_hidden(B_58, '#skF_12'))), inference(splitLeft, [status(thm)], [c_1335])).
% 3.78/1.61  tff(c_2194, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_2174, c_1336])).
% 3.78/1.61  tff(c_2212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2194])).
% 3.78/1.61  tff(c_2214, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_1335])).
% 3.78/1.61  tff(c_2240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2214, c_129])).
% 3.78/1.61  tff(c_2242, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_66])).
% 3.78/1.61  tff(c_2241, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_66])).
% 3.78/1.61  tff(c_2252, plain, ('#skF_13'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2242, c_2241])).
% 3.78/1.61  tff(c_2246, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_8])).
% 3.78/1.61  tff(c_2257, plain, (v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_2246])).
% 3.78/1.61  tff(c_2306, plain, (![A_250]: (v1_funct_1(A_250) | ~v1_xboole_0(A_250))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.78/1.61  tff(c_2310, plain, (v1_funct_1('#skF_12')), inference(resolution, [status(thm)], [c_2257, c_2306])).
% 3.78/1.61  tff(c_2244, plain, (k1_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_2241, c_52])).
% 3.78/1.61  tff(c_2263, plain, (k1_relat_1('#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_2252, c_2244])).
% 3.78/1.61  tff(c_2243, plain, (![A_6]: (r1_tarski('#skF_13', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_10])).
% 3.78/1.61  tff(c_2268, plain, (![A_6]: (r1_tarski('#skF_12', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_2243])).
% 3.78/1.61  tff(c_2245, plain, (k2_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_2241, c_50])).
% 3.78/1.61  tff(c_2270, plain, (k2_relat_1('#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_2252, c_2245])).
% 3.78/1.61  tff(c_2284, plain, (![C_248]: (~r1_tarski(k2_relat_1(C_248), '#skF_12') | k1_relat_1(C_248)!='#skF_12' | ~v1_funct_1(C_248) | ~v1_relat_1(C_248))), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_64])).
% 3.78/1.61  tff(c_2287, plain, (~r1_tarski('#skF_12', '#skF_12') | k1_relat_1('#skF_12')!='#skF_12' | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2270, c_2284])).
% 3.78/1.61  tff(c_2289, plain, (~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2263, c_2268, c_2287])).
% 3.78/1.61  tff(c_2312, plain, (~v1_relat_1('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2310, c_2289])).
% 3.78/1.61  tff(c_2331, plain, (![A_260]: (r2_hidden('#skF_4'(A_260), A_260) | v1_relat_1(A_260))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.78/1.61  tff(c_2290, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2242, c_2242, c_26])).
% 3.78/1.61  tff(c_2313, plain, (![A_251, B_252]: (~r2_hidden(A_251, k2_zfmisc_1(A_251, B_252)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.61  tff(c_2316, plain, (![A_12]: (~r2_hidden(A_12, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2290, c_2313])).
% 3.78/1.61  tff(c_2335, plain, (v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_2331, c_2316])).
% 3.78/1.61  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2312, c_2335])).
% 3.78/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.61  
% 3.78/1.61  Inference rules
% 3.78/1.61  ----------------------
% 3.78/1.61  #Ref     : 1
% 3.78/1.61  #Sup     : 461
% 3.78/1.61  #Fact    : 0
% 3.78/1.61  #Define  : 0
% 3.78/1.61  #Split   : 9
% 3.78/1.61  #Chain   : 0
% 3.78/1.61  #Close   : 0
% 3.78/1.61  
% 3.78/1.61  Ordering : KBO
% 3.78/1.61  
% 3.78/1.61  Simplification rules
% 3.78/1.61  ----------------------
% 3.78/1.61  #Subsume      : 76
% 3.78/1.61  #Demod        : 267
% 3.78/1.61  #Tautology    : 232
% 3.78/1.61  #SimpNegUnit  : 19
% 3.78/1.61  #BackRed      : 79
% 3.78/1.61  
% 3.78/1.61  #Partial instantiations: 0
% 3.78/1.61  #Strategies tried      : 1
% 3.78/1.61  
% 3.78/1.61  Timing (in seconds)
% 3.78/1.61  ----------------------
% 3.78/1.61  Preprocessing        : 0.32
% 3.78/1.61  Parsing              : 0.17
% 3.78/1.61  CNF conversion       : 0.03
% 3.78/1.61  Main loop            : 0.54
% 3.78/1.61  Inferencing          : 0.20
% 3.78/1.61  Reduction            : 0.17
% 3.78/1.61  Demodulation         : 0.11
% 3.78/1.61  BG Simplification    : 0.03
% 3.78/1.61  Subsumption          : 0.10
% 3.78/1.61  Abstraction          : 0.03
% 3.78/1.61  MUC search           : 0.00
% 3.78/1.61  Cooper               : 0.00
% 3.78/1.61  Total                : 0.90
% 3.78/1.61  Index Insertion      : 0.00
% 3.78/1.61  Index Deletion       : 0.00
% 3.78/1.61  Index Matching       : 0.00
% 3.78/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
