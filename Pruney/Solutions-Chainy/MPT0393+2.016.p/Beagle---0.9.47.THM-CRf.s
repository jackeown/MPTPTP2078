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
% DateTime   : Thu Dec  3 09:57:19 EST 2020

% Result     : Theorem 55.82s
% Output     : CNFRefutation 55.92s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 363 expanded)
%              Number of leaves         :   32 ( 135 expanded)
%              Depth                    :   17
%              Number of atoms          :  221 (1011 expanded)
%              Number of equality atoms :   72 ( 500 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_5 > #skF_10 > #skF_8 > #skF_7 > #skF_2 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_106,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_128,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_setfam_1(B_69),A_70)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_131,plain,(
    ! [A_70] :
      ( r1_tarski(k1_xboole_0,A_70)
      | ~ r2_hidden(A_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_128])).

tff(c_153,plain,(
    ! [B_75] :
      ( r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_75))
      | r1_tarski(k1_xboole_0,B_75) ) ),
    inference(resolution,[status(thm)],[c_144,c_131])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_213,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_479,plain,(
    ! [A_131,B_132,B_133] :
      ( r2_hidden('#skF_1'(A_131,B_132),B_133)
      | ~ r1_tarski(A_131,B_133)
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_6,c_213])).

tff(c_133,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_6'(A_72,B_73),B_73)
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_286,plain,(
    ! [A_105,A_106] :
      ( '#skF_6'(A_105,k1_tarski(A_106)) = A_106
      | ~ r2_hidden(A_105,k1_tarski(A_106)) ) ),
    inference(resolution,[status(thm)],[c_133,c_14])).

tff(c_300,plain,(
    ! [C_12] : '#skF_6'(C_12,k1_tarski(C_12)) = C_12 ),
    inference(resolution,[status(thm)],[c_16,c_286])).

tff(c_372,plain,(
    ! [D_117,A_118,B_119] :
      ( ~ r2_hidden(D_117,'#skF_6'(A_118,B_119))
      | ~ r2_hidden(D_117,B_119)
      | ~ r2_hidden(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_375,plain,(
    ! [D_117,C_12] :
      ( ~ r2_hidden(D_117,C_12)
      | ~ r2_hidden(D_117,k1_tarski(C_12))
      | ~ r2_hidden(C_12,k1_tarski(C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_372])).

tff(c_388,plain,(
    ! [D_120,C_121] :
      ( ~ r2_hidden(D_120,C_121)
      | ~ r2_hidden(D_120,k1_tarski(C_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_375])).

tff(c_402,plain,(
    ! [C_12] : ~ r2_hidden(C_12,C_12) ),
    inference(resolution,[status(thm)],[c_16,c_388])).

tff(c_551,plain,(
    ! [A_136,B_137] :
      ( ~ r1_tarski(A_136,'#skF_1'(A_136,B_137))
      | r1_tarski(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_479,c_402])).

tff(c_567,plain,(
    ! [B_75] : r1_tarski(k1_xboole_0,B_75) ),
    inference(resolution,[status(thm)],[c_153,c_551])).

tff(c_1776,plain,(
    ! [A_194,B_195,D_196] :
      ( r2_hidden('#skF_8'(A_194,B_195),D_196)
      | ~ r2_hidden(D_196,A_194)
      | r2_hidden('#skF_10'(A_194,B_195),A_194)
      | k1_setfam_1(A_194) = B_195
      | k1_xboole_0 = A_194 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_8'(A_35,B_36),B_36)
      | r2_hidden('#skF_10'(A_35,B_36),A_35)
      | k1_setfam_1(A_35) = B_36
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8583,plain,(
    ! [D_13256,A_13257] :
      ( ~ r2_hidden(D_13256,A_13257)
      | r2_hidden('#skF_10'(A_13257,D_13256),A_13257)
      | k1_setfam_1(A_13257) = D_13256
      | k1_xboole_0 = A_13257 ) ),
    inference(resolution,[status(thm)],[c_1776,c_64])).

tff(c_277204,plain,(
    ! [A_149386,D_149387] :
      ( '#skF_10'(k1_tarski(A_149386),D_149387) = A_149386
      | ~ r2_hidden(D_149387,k1_tarski(A_149386))
      | k1_setfam_1(k1_tarski(A_149386)) = D_149387
      | k1_tarski(A_149386) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8583,c_14])).

tff(c_277496,plain,(
    ! [C_149496] :
      ( '#skF_10'(k1_tarski(C_149496),C_149496) = C_149496
      | k1_setfam_1(k1_tarski(C_149496)) = C_149496
      | k1_tarski(C_149496) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_277204])).

tff(c_84,plain,(
    k1_setfam_1(k1_tarski('#skF_11')) != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_278417,plain,
    ( '#skF_10'(k1_tarski('#skF_11'),'#skF_11') = '#skF_11'
    | k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_277496,c_84])).

tff(c_278424,plain,(
    k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_278417])).

tff(c_30,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k1_setfam_1(B_55),A_54)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_256,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden(A_99,B_100)
      | ~ r2_hidden(A_99,k4_xboole_0(B_100,k1_tarski(C_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10287,plain,(
    ! [B_15454,C_15455,B_15456] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_15454,k1_tarski(C_15455)),B_15456),B_15454)
      | r1_tarski(k4_xboole_0(B_15454,k1_tarski(C_15455)),B_15456) ) ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10452,plain,(
    ! [B_15454,C_15455] : r1_tarski(k4_xboole_0(B_15454,k1_tarski(C_15455)),B_15454) ),
    inference(resolution,[status(thm)],[c_10287,c_4])).

tff(c_267,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden(A_102,k4_xboole_0(B_103,k1_tarski(C_104)))
      | C_104 = A_102
      | ~ r2_hidden(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50694,plain,(
    ! [A_42632,B_42633,C_42634] :
      ( r1_tarski(A_42632,k4_xboole_0(B_42633,k1_tarski(C_42634)))
      | '#skF_1'(A_42632,k4_xboole_0(B_42633,k1_tarski(C_42634))) = C_42634
      | ~ r2_hidden('#skF_1'(A_42632,k4_xboole_0(B_42633,k1_tarski(C_42634))),B_42633) ) ),
    inference(resolution,[status(thm)],[c_267,c_4])).

tff(c_50927,plain,(
    ! [A_42855,C_42856] :
      ( '#skF_1'(A_42855,k4_xboole_0(A_42855,k1_tarski(C_42856))) = C_42856
      | r1_tarski(A_42855,k4_xboole_0(A_42855,k1_tarski(C_42856))) ) ),
    inference(resolution,[status(thm)],[c_6,c_50694])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50973,plain,(
    ! [A_42855,C_42856] :
      ( k4_xboole_0(A_42855,k1_tarski(C_42856)) = A_42855
      | ~ r1_tarski(k4_xboole_0(A_42855,k1_tarski(C_42856)),A_42855)
      | '#skF_1'(A_42855,k4_xboole_0(A_42855,k1_tarski(C_42856))) = C_42856 ) ),
    inference(resolution,[status(thm)],[c_50927,c_8])).

tff(c_51096,plain,(
    ! [A_42965,C_42966] :
      ( k4_xboole_0(A_42965,k1_tarski(C_42966)) = A_42965
      | '#skF_1'(A_42965,k4_xboole_0(A_42965,k1_tarski(C_42966))) = C_42966 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10452,c_50973])).

tff(c_534,plain,(
    ! [A_131,B_132] :
      ( ~ r1_tarski(A_131,'#skF_1'(A_131,B_132))
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_479,c_402])).

tff(c_248380,plain,(
    ! [A_136903,C_136904] :
      ( ~ r1_tarski(A_136903,C_136904)
      | r1_tarski(A_136903,k4_xboole_0(A_136903,k1_tarski(C_136904)))
      | k4_xboole_0(A_136903,k1_tarski(C_136904)) = A_136903 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51096,c_534])).

tff(c_10454,plain,(
    ! [B_15565,C_15566] : r1_tarski(k4_xboole_0(B_15565,k1_tarski(C_15566)),B_15565) ),
    inference(resolution,[status(thm)],[c_10287,c_4])).

tff(c_10563,plain,(
    ! [B_15565,C_15566] :
      ( k4_xboole_0(B_15565,k1_tarski(C_15566)) = B_15565
      | ~ r1_tarski(B_15565,k4_xboole_0(B_15565,k1_tarski(C_15566))) ) ),
    inference(resolution,[status(thm)],[c_10454,c_8])).

tff(c_248650,plain,(
    ! [A_137013,C_137014] :
      ( ~ r1_tarski(A_137013,C_137014)
      | k4_xboole_0(A_137013,k1_tarski(C_137014)) = A_137013 ) ),
    inference(resolution,[status(thm)],[c_248380,c_10563])).

tff(c_58,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_6'(A_28,B_29),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2689,plain,(
    ! [A_2814,B_2815,B_2816] :
      ( r2_hidden('#skF_6'(A_2814,B_2815),B_2816)
      | ~ r1_tarski(B_2815,B_2816)
      | ~ r2_hidden(A_2814,B_2815) ) ),
    inference(resolution,[status(thm)],[c_58,c_213])).

tff(c_52,plain,(
    ! [C_27,B_26] : ~ r2_hidden(C_27,k4_xboole_0(B_26,k1_tarski(C_27))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2759,plain,(
    ! [B_2815,B_26,A_2814] :
      ( ~ r1_tarski(B_2815,k4_xboole_0(B_26,k1_tarski('#skF_6'(A_2814,B_2815))))
      | ~ r2_hidden(A_2814,B_2815) ) ),
    inference(resolution,[status(thm)],[c_2689,c_52])).

tff(c_252183,plain,(
    ! [B_138226,A_138227,A_138228] :
      ( ~ r1_tarski(B_138226,A_138227)
      | ~ r2_hidden(A_138228,B_138226)
      | ~ r1_tarski(A_138227,'#skF_6'(A_138228,B_138226)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248650,c_2759])).

tff(c_256523,plain,(
    ! [B_139996,B_139997,A_139998] :
      ( ~ r1_tarski(B_139996,k1_setfam_1(B_139997))
      | ~ r2_hidden(A_139998,B_139996)
      | ~ r2_hidden('#skF_6'(A_139998,B_139996),B_139997) ) ),
    inference(resolution,[status(thm)],[c_82,c_252183])).

tff(c_263840,plain,(
    ! [B_142637,A_142638,B_142639] :
      ( ~ r1_tarski(B_142637,k1_setfam_1(k2_tarski('#skF_6'(A_142638,B_142637),B_142639)))
      | ~ r2_hidden(A_142638,B_142637) ) ),
    inference(resolution,[status(thm)],[c_30,c_256523])).

tff(c_264111,plain,(
    ! [C_12,B_142639] :
      ( ~ r1_tarski(k1_tarski(C_12),k1_setfam_1(k2_tarski(C_12,B_142639)))
      | ~ r2_hidden(C_12,k1_tarski(C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_263840])).

tff(c_264177,plain,(
    ! [C_12,B_142639] : ~ r1_tarski(k1_tarski(C_12),k1_setfam_1(k2_tarski(C_12,B_142639))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_264111])).

tff(c_278484,plain,(
    ! [B_142639] : ~ r1_tarski(k1_xboole_0,k1_setfam_1(k2_tarski('#skF_11',B_142639))) ),
    inference(superposition,[status(thm),theory(equality)],[c_278424,c_264177])).

tff(c_279440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_278484])).

tff(c_279442,plain,(
    k1_tarski('#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_278417])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_279441,plain,(
    '#skF_10'(k1_tarski('#skF_11'),'#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_278417])).

tff(c_1928,plain,(
    ! [A_199,B_200,D_201] :
      ( r2_hidden('#skF_8'(A_199,B_200),D_201)
      | ~ r2_hidden(D_201,A_199)
      | r2_hidden('#skF_9'(A_199,B_200),B_200)
      | k1_setfam_1(A_199) = B_200
      | k1_xboole_0 = A_199 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2029,plain,(
    ! [A_199,B_200,B_2,D_201] :
      ( r2_hidden('#skF_9'(A_199,B_200),B_2)
      | ~ r1_tarski(B_200,B_2)
      | r2_hidden('#skF_8'(A_199,B_200),D_201)
      | ~ r2_hidden(D_201,A_199)
      | k1_setfam_1(A_199) = B_200
      | k1_xboole_0 = A_199 ) ),
    inference(resolution,[status(thm)],[c_1928,c_2])).

tff(c_68,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_8'(A_35,B_36),B_36)
      | r2_hidden('#skF_9'(A_35,B_36),B_36)
      | k1_setfam_1(A_35) = B_36
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2010,plain,(
    ! [D_201,A_199] :
      ( ~ r2_hidden(D_201,A_199)
      | r2_hidden('#skF_9'(A_199,D_201),D_201)
      | k1_setfam_1(A_199) = D_201
      | k1_xboole_0 = A_199 ) ),
    inference(resolution,[status(thm)],[c_1928,c_68])).

tff(c_60,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_8'(A_35,B_36),B_36)
      | ~ r2_hidden('#skF_9'(A_35,B_36),'#skF_10'(A_35,B_36))
      | k1_setfam_1(A_35) = B_36
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_279471,plain,
    ( ~ r2_hidden('#skF_8'(k1_tarski('#skF_11'),'#skF_11'),'#skF_11')
    | ~ r2_hidden('#skF_9'(k1_tarski('#skF_11'),'#skF_11'),'#skF_11')
    | k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
    | k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_279441,c_60])).

tff(c_279530,plain,
    ( ~ r2_hidden('#skF_8'(k1_tarski('#skF_11'),'#skF_11'),'#skF_11')
    | ~ r2_hidden('#skF_9'(k1_tarski('#skF_11'),'#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_279442,c_84,c_279471])).

tff(c_279833,plain,(
    ~ r2_hidden('#skF_9'(k1_tarski('#skF_11'),'#skF_11'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_279530])).

tff(c_279853,plain,
    ( ~ r2_hidden('#skF_11',k1_tarski('#skF_11'))
    | k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
    | k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2010,c_279833])).

tff(c_279871,plain,
    ( k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
    | k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_279853])).

tff(c_279873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279442,c_84,c_279871])).

tff(c_279874,plain,(
    ~ r2_hidden('#skF_8'(k1_tarski('#skF_11'),'#skF_11'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_279530])).

tff(c_279882,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_9'(k1_tarski('#skF_11'),'#skF_11'),B_2)
      | ~ r1_tarski('#skF_11',B_2)
      | ~ r2_hidden('#skF_11',k1_tarski('#skF_11'))
      | k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
      | k1_tarski('#skF_11') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2029,c_279874])).

tff(c_279913,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_9'(k1_tarski('#skF_11'),'#skF_11'),B_2)
      | ~ r1_tarski('#skF_11',B_2)
      | k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
      | k1_tarski('#skF_11') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_279882])).

tff(c_280152,plain,(
    ! [B_150582] :
      ( r2_hidden('#skF_9'(k1_tarski('#skF_11'),'#skF_11'),B_150582)
      | ~ r1_tarski('#skF_11',B_150582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_279442,c_84,c_279913])).

tff(c_62,plain,(
    ! [A_35,B_36,D_52] :
      ( r2_hidden('#skF_8'(A_35,B_36),D_52)
      | ~ r2_hidden(D_52,A_35)
      | ~ r2_hidden('#skF_9'(A_35,B_36),'#skF_10'(A_35,B_36))
      | k1_setfam_1(A_35) = B_36
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_280561,plain,(
    ! [D_52] :
      ( r2_hidden('#skF_8'(k1_tarski('#skF_11'),'#skF_11'),D_52)
      | ~ r2_hidden(D_52,k1_tarski('#skF_11'))
      | k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
      | k1_tarski('#skF_11') = k1_xboole_0
      | ~ r1_tarski('#skF_11','#skF_10'(k1_tarski('#skF_11'),'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_280152,c_62])).

tff(c_280785,plain,(
    ! [D_52] :
      ( r2_hidden('#skF_8'(k1_tarski('#skF_11'),'#skF_11'),D_52)
      | ~ r2_hidden(D_52,k1_tarski('#skF_11'))
      | k1_setfam_1(k1_tarski('#skF_11')) = '#skF_11'
      | k1_tarski('#skF_11') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_279441,c_280561])).

tff(c_281579,plain,(
    ! [D_151344] :
      ( r2_hidden('#skF_8'(k1_tarski('#skF_11'),'#skF_11'),D_151344)
      | ~ r2_hidden(D_151344,k1_tarski('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_279442,c_84,c_280785])).

tff(c_281582,plain,(
    ~ r2_hidden('#skF_11',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_281579,c_279874])).

tff(c_282100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_281582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 55.82/44.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.92/44.26  
% 55.92/44.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.92/44.26  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_5 > #skF_10 > #skF_8 > #skF_7 > #skF_2 > #skF_1 > #skF_9
% 55.92/44.26  
% 55.92/44.26  %Foreground sorts:
% 55.92/44.26  
% 55.92/44.26  
% 55.92/44.26  %Background operators:
% 55.92/44.26  
% 55.92/44.26  
% 55.92/44.26  %Foreground operators:
% 55.92/44.26  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 55.92/44.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 55.92/44.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 55.92/44.26  tff('#skF_11', type, '#skF_11': $i).
% 55.92/44.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 55.92/44.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 55.92/44.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 55.92/44.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 55.92/44.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 55.92/44.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 55.92/44.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 55.92/44.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 55.92/44.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 55.92/44.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 55.92/44.26  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 55.92/44.26  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 55.92/44.26  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 55.92/44.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 55.92/44.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 55.92/44.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 55.92/44.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 55.92/44.26  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 55.92/44.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 55.92/44.26  
% 55.92/44.28  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 55.92/44.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 55.92/44.28  tff(f_99, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 55.92/44.28  tff(f_103, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 55.92/44.28  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 55.92/44.28  tff(f_106, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 55.92/44.28  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 55.92/44.28  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 55.92/44.28  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 55.92/44.28  tff(c_16, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 55.92/44.28  tff(c_144, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 55.92/44.28  tff(c_80, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_128, plain, (![B_69, A_70]: (r1_tarski(k1_setfam_1(B_69), A_70) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_103])).
% 55.92/44.28  tff(c_131, plain, (![A_70]: (r1_tarski(k1_xboole_0, A_70) | ~r2_hidden(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_80, c_128])).
% 55.92/44.28  tff(c_153, plain, (![B_75]: (r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_75)) | r1_tarski(k1_xboole_0, B_75))), inference(resolution, [status(thm)], [c_144, c_131])).
% 55.92/44.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 55.92/44.28  tff(c_213, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 55.92/44.28  tff(c_479, plain, (![A_131, B_132, B_133]: (r2_hidden('#skF_1'(A_131, B_132), B_133) | ~r1_tarski(A_131, B_133) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_6, c_213])).
% 55.92/44.28  tff(c_133, plain, (![A_72, B_73]: (r2_hidden('#skF_6'(A_72, B_73), B_73) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_80])).
% 55.92/44.28  tff(c_14, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 55.92/44.28  tff(c_286, plain, (![A_105, A_106]: ('#skF_6'(A_105, k1_tarski(A_106))=A_106 | ~r2_hidden(A_105, k1_tarski(A_106)))), inference(resolution, [status(thm)], [c_133, c_14])).
% 55.92/44.28  tff(c_300, plain, (![C_12]: ('#skF_6'(C_12, k1_tarski(C_12))=C_12)), inference(resolution, [status(thm)], [c_16, c_286])).
% 55.92/44.28  tff(c_372, plain, (![D_117, A_118, B_119]: (~r2_hidden(D_117, '#skF_6'(A_118, B_119)) | ~r2_hidden(D_117, B_119) | ~r2_hidden(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_80])).
% 55.92/44.28  tff(c_375, plain, (![D_117, C_12]: (~r2_hidden(D_117, C_12) | ~r2_hidden(D_117, k1_tarski(C_12)) | ~r2_hidden(C_12, k1_tarski(C_12)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_372])).
% 55.92/44.28  tff(c_388, plain, (![D_120, C_121]: (~r2_hidden(D_120, C_121) | ~r2_hidden(D_120, k1_tarski(C_121)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_375])).
% 55.92/44.28  tff(c_402, plain, (![C_12]: (~r2_hidden(C_12, C_12))), inference(resolution, [status(thm)], [c_16, c_388])).
% 55.92/44.28  tff(c_551, plain, (![A_136, B_137]: (~r1_tarski(A_136, '#skF_1'(A_136, B_137)) | r1_tarski(A_136, B_137))), inference(resolution, [status(thm)], [c_479, c_402])).
% 55.92/44.28  tff(c_567, plain, (![B_75]: (r1_tarski(k1_xboole_0, B_75))), inference(resolution, [status(thm)], [c_153, c_551])).
% 55.92/44.28  tff(c_1776, plain, (![A_194, B_195, D_196]: (r2_hidden('#skF_8'(A_194, B_195), D_196) | ~r2_hidden(D_196, A_194) | r2_hidden('#skF_10'(A_194, B_195), A_194) | k1_setfam_1(A_194)=B_195 | k1_xboole_0=A_194)), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_64, plain, (![A_35, B_36]: (~r2_hidden('#skF_8'(A_35, B_36), B_36) | r2_hidden('#skF_10'(A_35, B_36), A_35) | k1_setfam_1(A_35)=B_36 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_8583, plain, (![D_13256, A_13257]: (~r2_hidden(D_13256, A_13257) | r2_hidden('#skF_10'(A_13257, D_13256), A_13257) | k1_setfam_1(A_13257)=D_13256 | k1_xboole_0=A_13257)), inference(resolution, [status(thm)], [c_1776, c_64])).
% 55.92/44.28  tff(c_277204, plain, (![A_149386, D_149387]: ('#skF_10'(k1_tarski(A_149386), D_149387)=A_149386 | ~r2_hidden(D_149387, k1_tarski(A_149386)) | k1_setfam_1(k1_tarski(A_149386))=D_149387 | k1_tarski(A_149386)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8583, c_14])).
% 55.92/44.28  tff(c_277496, plain, (![C_149496]: ('#skF_10'(k1_tarski(C_149496), C_149496)=C_149496 | k1_setfam_1(k1_tarski(C_149496))=C_149496 | k1_tarski(C_149496)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_277204])).
% 55.92/44.28  tff(c_84, plain, (k1_setfam_1(k1_tarski('#skF_11'))!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_106])).
% 55.92/44.28  tff(c_278417, plain, ('#skF_10'(k1_tarski('#skF_11'), '#skF_11')='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_277496, c_84])).
% 55.92/44.28  tff(c_278424, plain, (k1_tarski('#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_278417])).
% 55.92/44.28  tff(c_30, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 55.92/44.28  tff(c_82, plain, (![B_55, A_54]: (r1_tarski(k1_setfam_1(B_55), A_54) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_103])).
% 55.92/44.28  tff(c_256, plain, (![A_99, B_100, C_101]: (r2_hidden(A_99, B_100) | ~r2_hidden(A_99, k4_xboole_0(B_100, k1_tarski(C_101))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 55.92/44.28  tff(c_10287, plain, (![B_15454, C_15455, B_15456]: (r2_hidden('#skF_1'(k4_xboole_0(B_15454, k1_tarski(C_15455)), B_15456), B_15454) | r1_tarski(k4_xboole_0(B_15454, k1_tarski(C_15455)), B_15456))), inference(resolution, [status(thm)], [c_6, c_256])).
% 55.92/44.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 55.92/44.28  tff(c_10452, plain, (![B_15454, C_15455]: (r1_tarski(k4_xboole_0(B_15454, k1_tarski(C_15455)), B_15454))), inference(resolution, [status(thm)], [c_10287, c_4])).
% 55.92/44.28  tff(c_267, plain, (![A_102, B_103, C_104]: (r2_hidden(A_102, k4_xboole_0(B_103, k1_tarski(C_104))) | C_104=A_102 | ~r2_hidden(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_67])).
% 55.92/44.28  tff(c_50694, plain, (![A_42632, B_42633, C_42634]: (r1_tarski(A_42632, k4_xboole_0(B_42633, k1_tarski(C_42634))) | '#skF_1'(A_42632, k4_xboole_0(B_42633, k1_tarski(C_42634)))=C_42634 | ~r2_hidden('#skF_1'(A_42632, k4_xboole_0(B_42633, k1_tarski(C_42634))), B_42633))), inference(resolution, [status(thm)], [c_267, c_4])).
% 55.92/44.28  tff(c_50927, plain, (![A_42855, C_42856]: ('#skF_1'(A_42855, k4_xboole_0(A_42855, k1_tarski(C_42856)))=C_42856 | r1_tarski(A_42855, k4_xboole_0(A_42855, k1_tarski(C_42856))))), inference(resolution, [status(thm)], [c_6, c_50694])).
% 55.92/44.28  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 55.92/44.28  tff(c_50973, plain, (![A_42855, C_42856]: (k4_xboole_0(A_42855, k1_tarski(C_42856))=A_42855 | ~r1_tarski(k4_xboole_0(A_42855, k1_tarski(C_42856)), A_42855) | '#skF_1'(A_42855, k4_xboole_0(A_42855, k1_tarski(C_42856)))=C_42856)), inference(resolution, [status(thm)], [c_50927, c_8])).
% 55.92/44.28  tff(c_51096, plain, (![A_42965, C_42966]: (k4_xboole_0(A_42965, k1_tarski(C_42966))=A_42965 | '#skF_1'(A_42965, k4_xboole_0(A_42965, k1_tarski(C_42966)))=C_42966)), inference(demodulation, [status(thm), theory('equality')], [c_10452, c_50973])).
% 55.92/44.28  tff(c_534, plain, (![A_131, B_132]: (~r1_tarski(A_131, '#skF_1'(A_131, B_132)) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_479, c_402])).
% 55.92/44.28  tff(c_248380, plain, (![A_136903, C_136904]: (~r1_tarski(A_136903, C_136904) | r1_tarski(A_136903, k4_xboole_0(A_136903, k1_tarski(C_136904))) | k4_xboole_0(A_136903, k1_tarski(C_136904))=A_136903)), inference(superposition, [status(thm), theory('equality')], [c_51096, c_534])).
% 55.92/44.28  tff(c_10454, plain, (![B_15565, C_15566]: (r1_tarski(k4_xboole_0(B_15565, k1_tarski(C_15566)), B_15565))), inference(resolution, [status(thm)], [c_10287, c_4])).
% 55.92/44.28  tff(c_10563, plain, (![B_15565, C_15566]: (k4_xboole_0(B_15565, k1_tarski(C_15566))=B_15565 | ~r1_tarski(B_15565, k4_xboole_0(B_15565, k1_tarski(C_15566))))), inference(resolution, [status(thm)], [c_10454, c_8])).
% 55.92/44.28  tff(c_248650, plain, (![A_137013, C_137014]: (~r1_tarski(A_137013, C_137014) | k4_xboole_0(A_137013, k1_tarski(C_137014))=A_137013)), inference(resolution, [status(thm)], [c_248380, c_10563])).
% 55.92/44.28  tff(c_58, plain, (![A_28, B_29]: (r2_hidden('#skF_6'(A_28, B_29), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 55.92/44.28  tff(c_2689, plain, (![A_2814, B_2815, B_2816]: (r2_hidden('#skF_6'(A_2814, B_2815), B_2816) | ~r1_tarski(B_2815, B_2816) | ~r2_hidden(A_2814, B_2815))), inference(resolution, [status(thm)], [c_58, c_213])).
% 55.92/44.28  tff(c_52, plain, (![C_27, B_26]: (~r2_hidden(C_27, k4_xboole_0(B_26, k1_tarski(C_27))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 55.92/44.28  tff(c_2759, plain, (![B_2815, B_26, A_2814]: (~r1_tarski(B_2815, k4_xboole_0(B_26, k1_tarski('#skF_6'(A_2814, B_2815)))) | ~r2_hidden(A_2814, B_2815))), inference(resolution, [status(thm)], [c_2689, c_52])).
% 55.92/44.28  tff(c_252183, plain, (![B_138226, A_138227, A_138228]: (~r1_tarski(B_138226, A_138227) | ~r2_hidden(A_138228, B_138226) | ~r1_tarski(A_138227, '#skF_6'(A_138228, B_138226)))), inference(superposition, [status(thm), theory('equality')], [c_248650, c_2759])).
% 55.92/44.28  tff(c_256523, plain, (![B_139996, B_139997, A_139998]: (~r1_tarski(B_139996, k1_setfam_1(B_139997)) | ~r2_hidden(A_139998, B_139996) | ~r2_hidden('#skF_6'(A_139998, B_139996), B_139997))), inference(resolution, [status(thm)], [c_82, c_252183])).
% 55.92/44.28  tff(c_263840, plain, (![B_142637, A_142638, B_142639]: (~r1_tarski(B_142637, k1_setfam_1(k2_tarski('#skF_6'(A_142638, B_142637), B_142639))) | ~r2_hidden(A_142638, B_142637))), inference(resolution, [status(thm)], [c_30, c_256523])).
% 55.92/44.28  tff(c_264111, plain, (![C_12, B_142639]: (~r1_tarski(k1_tarski(C_12), k1_setfam_1(k2_tarski(C_12, B_142639))) | ~r2_hidden(C_12, k1_tarski(C_12)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_263840])).
% 55.92/44.28  tff(c_264177, plain, (![C_12, B_142639]: (~r1_tarski(k1_tarski(C_12), k1_setfam_1(k2_tarski(C_12, B_142639))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_264111])).
% 55.92/44.28  tff(c_278484, plain, (![B_142639]: (~r1_tarski(k1_xboole_0, k1_setfam_1(k2_tarski('#skF_11', B_142639))))), inference(superposition, [status(thm), theory('equality')], [c_278424, c_264177])).
% 55.92/44.28  tff(c_279440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_567, c_278484])).
% 55.92/44.28  tff(c_279442, plain, (k1_tarski('#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_278417])).
% 55.92/44.28  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 55.92/44.28  tff(c_279441, plain, ('#skF_10'(k1_tarski('#skF_11'), '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_278417])).
% 55.92/44.28  tff(c_1928, plain, (![A_199, B_200, D_201]: (r2_hidden('#skF_8'(A_199, B_200), D_201) | ~r2_hidden(D_201, A_199) | r2_hidden('#skF_9'(A_199, B_200), B_200) | k1_setfam_1(A_199)=B_200 | k1_xboole_0=A_199)), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 55.92/44.28  tff(c_2029, plain, (![A_199, B_200, B_2, D_201]: (r2_hidden('#skF_9'(A_199, B_200), B_2) | ~r1_tarski(B_200, B_2) | r2_hidden('#skF_8'(A_199, B_200), D_201) | ~r2_hidden(D_201, A_199) | k1_setfam_1(A_199)=B_200 | k1_xboole_0=A_199)), inference(resolution, [status(thm)], [c_1928, c_2])).
% 55.92/44.28  tff(c_68, plain, (![A_35, B_36]: (~r2_hidden('#skF_8'(A_35, B_36), B_36) | r2_hidden('#skF_9'(A_35, B_36), B_36) | k1_setfam_1(A_35)=B_36 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_2010, plain, (![D_201, A_199]: (~r2_hidden(D_201, A_199) | r2_hidden('#skF_9'(A_199, D_201), D_201) | k1_setfam_1(A_199)=D_201 | k1_xboole_0=A_199)), inference(resolution, [status(thm)], [c_1928, c_68])).
% 55.92/44.28  tff(c_60, plain, (![A_35, B_36]: (~r2_hidden('#skF_8'(A_35, B_36), B_36) | ~r2_hidden('#skF_9'(A_35, B_36), '#skF_10'(A_35, B_36)) | k1_setfam_1(A_35)=B_36 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_279471, plain, (~r2_hidden('#skF_8'(k1_tarski('#skF_11'), '#skF_11'), '#skF_11') | ~r2_hidden('#skF_9'(k1_tarski('#skF_11'), '#skF_11'), '#skF_11') | k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_279441, c_60])).
% 55.92/44.28  tff(c_279530, plain, (~r2_hidden('#skF_8'(k1_tarski('#skF_11'), '#skF_11'), '#skF_11') | ~r2_hidden('#skF_9'(k1_tarski('#skF_11'), '#skF_11'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_279442, c_84, c_279471])).
% 55.92/44.28  tff(c_279833, plain, (~r2_hidden('#skF_9'(k1_tarski('#skF_11'), '#skF_11'), '#skF_11')), inference(splitLeft, [status(thm)], [c_279530])).
% 55.92/44.28  tff(c_279853, plain, (~r2_hidden('#skF_11', k1_tarski('#skF_11')) | k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_2010, c_279833])).
% 55.92/44.28  tff(c_279871, plain, (k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_279853])).
% 55.92/44.28  tff(c_279873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279442, c_84, c_279871])).
% 55.92/44.28  tff(c_279874, plain, (~r2_hidden('#skF_8'(k1_tarski('#skF_11'), '#skF_11'), '#skF_11')), inference(splitRight, [status(thm)], [c_279530])).
% 55.92/44.28  tff(c_279882, plain, (![B_2]: (r2_hidden('#skF_9'(k1_tarski('#skF_11'), '#skF_11'), B_2) | ~r1_tarski('#skF_11', B_2) | ~r2_hidden('#skF_11', k1_tarski('#skF_11')) | k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2029, c_279874])).
% 55.92/44.28  tff(c_279913, plain, (![B_2]: (r2_hidden('#skF_9'(k1_tarski('#skF_11'), '#skF_11'), B_2) | ~r1_tarski('#skF_11', B_2) | k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_279882])).
% 55.92/44.28  tff(c_280152, plain, (![B_150582]: (r2_hidden('#skF_9'(k1_tarski('#skF_11'), '#skF_11'), B_150582) | ~r1_tarski('#skF_11', B_150582))), inference(negUnitSimplification, [status(thm)], [c_279442, c_84, c_279913])).
% 55.92/44.28  tff(c_62, plain, (![A_35, B_36, D_52]: (r2_hidden('#skF_8'(A_35, B_36), D_52) | ~r2_hidden(D_52, A_35) | ~r2_hidden('#skF_9'(A_35, B_36), '#skF_10'(A_35, B_36)) | k1_setfam_1(A_35)=B_36 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_99])).
% 55.92/44.28  tff(c_280561, plain, (![D_52]: (r2_hidden('#skF_8'(k1_tarski('#skF_11'), '#skF_11'), D_52) | ~r2_hidden(D_52, k1_tarski('#skF_11')) | k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0 | ~r1_tarski('#skF_11', '#skF_10'(k1_tarski('#skF_11'), '#skF_11')))), inference(resolution, [status(thm)], [c_280152, c_62])).
% 55.92/44.28  tff(c_280785, plain, (![D_52]: (r2_hidden('#skF_8'(k1_tarski('#skF_11'), '#skF_11'), D_52) | ~r2_hidden(D_52, k1_tarski('#skF_11')) | k1_setfam_1(k1_tarski('#skF_11'))='#skF_11' | k1_tarski('#skF_11')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_279441, c_280561])).
% 55.92/44.28  tff(c_281579, plain, (![D_151344]: (r2_hidden('#skF_8'(k1_tarski('#skF_11'), '#skF_11'), D_151344) | ~r2_hidden(D_151344, k1_tarski('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_279442, c_84, c_280785])).
% 55.92/44.28  tff(c_281582, plain, (~r2_hidden('#skF_11', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_281579, c_279874])).
% 55.92/44.28  tff(c_282100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_281582])).
% 55.92/44.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.92/44.28  
% 55.92/44.28  Inference rules
% 55.92/44.28  ----------------------
% 55.92/44.28  #Ref     : 0
% 55.92/44.28  #Sup     : 62466
% 55.92/44.28  #Fact    : 176
% 55.92/44.28  #Define  : 0
% 55.92/44.28  #Split   : 28
% 55.92/44.28  #Chain   : 0
% 55.92/44.28  #Close   : 0
% 55.92/44.28  
% 55.92/44.28  Ordering : KBO
% 55.92/44.28  
% 55.92/44.28  Simplification rules
% 55.92/44.28  ----------------------
% 55.92/44.28  #Subsume      : 33553
% 55.92/44.28  #Demod        : 16125
% 55.92/44.29  #Tautology    : 6858
% 55.92/44.29  #SimpNegUnit  : 1630
% 55.92/44.29  #BackRed      : 37
% 55.92/44.29  
% 55.92/44.29  #Partial instantiations: 74340
% 55.92/44.29  #Strategies tried      : 1
% 55.92/44.29  
% 55.92/44.29  Timing (in seconds)
% 55.92/44.29  ----------------------
% 55.92/44.29  Preprocessing        : 0.33
% 55.92/44.29  Parsing              : 0.17
% 55.92/44.29  CNF conversion       : 0.03
% 55.92/44.29  Main loop            : 43.16
% 55.92/44.29  Inferencing          : 6.54
% 55.92/44.29  Reduction            : 9.31
% 55.92/44.29  Demodulation         : 5.85
% 55.92/44.29  BG Simplification    : 0.57
% 55.92/44.29  Subsumption          : 24.15
% 55.92/44.29  Abstraction          : 1.26
% 55.92/44.29  MUC search           : 0.00
% 55.92/44.29  Cooper               : 0.00
% 55.92/44.29  Total                : 43.53
% 55.92/44.29  Index Insertion      : 0.00
% 55.92/44.29  Index Deletion       : 0.00
% 55.92/44.29  Index Matching       : 0.00
% 55.92/44.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
