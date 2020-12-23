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
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 183 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 402 expanded)
%              Number of equality atoms :   15 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_10','#skF_12')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_5'(A_12,B_13,C_14),B_13)
      | r2_hidden('#skF_6'(A_12,B_13,C_14),C_14)
      | k2_zfmisc_1(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,B_70)
      | ~ r2_hidden(C_71,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [C_76,A_77] :
      ( ~ r2_hidden(C_76,k1_xboole_0)
      | ~ r2_hidden(C_76,A_77) ) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_182,plain,(
    ! [B_97,A_98] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_97),A_98)
      | r1_tarski(k1_xboole_0,B_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_187,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_50,plain,(
    ! [B_51] : k2_zfmisc_1(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_203,plain,(
    ! [A_103,B_104,D_105] :
      ( r2_hidden('#skF_8'(A_103,B_104,k2_zfmisc_1(A_103,B_104),D_105),B_104)
      | ~ r2_hidden(D_105,k2_zfmisc_1(A_103,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_216,plain,(
    ! [B_51,D_105] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_51,k1_xboole_0,D_105),B_51)
      | ~ r2_hidden(D_105,k2_zfmisc_1(k1_xboole_0,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_203])).

tff(c_235,plain,(
    ! [B_108,D_109] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_108,k1_xboole_0,D_109),B_108)
      | ~ r2_hidden(D_109,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_216])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_775,plain,(
    ! [B_207,D_208,B_209] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_207,k1_xboole_0,D_208),B_209)
      | ~ r1_tarski(B_207,B_209)
      | ~ r2_hidden(D_208,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_48,plain,(
    ! [A_50] : k2_zfmisc_1(A_50,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,(
    ! [C_71,A_11] :
      ( ~ r2_hidden(C_71,k1_xboole_0)
      | ~ r2_hidden(C_71,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_208,plain,(
    ! [A_103,D_105,A_11] :
      ( ~ r2_hidden('#skF_8'(A_103,k1_xboole_0,k2_zfmisc_1(A_103,k1_xboole_0),D_105),A_11)
      | ~ r2_hidden(D_105,k2_zfmisc_1(A_103,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_203,c_115])).

tff(c_219,plain,(
    ! [A_103,D_105,A_11] :
      ( ~ r2_hidden('#skF_8'(A_103,k1_xboole_0,k1_xboole_0,D_105),A_11)
      | ~ r2_hidden(D_105,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_208])).

tff(c_785,plain,(
    ! [B_209,D_208] :
      ( ~ r1_tarski(k1_xboole_0,B_209)
      | ~ r2_hidden(D_208,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_775,c_219])).

tff(c_804,plain,(
    ! [D_210] : ~ r2_hidden(D_210,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_785])).

tff(c_858,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_5'(A_12,B_13,k1_xboole_0),B_13)
      | k2_zfmisc_1(A_12,B_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_804])).

tff(c_56,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_164,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_hidden(k4_tarski(A_93,B_94),k2_zfmisc_1(C_95,D_96))
      | ~ r2_hidden(B_94,D_96)
      | ~ r2_hidden(A_93,C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1069,plain,(
    ! [B_261,C_263,D_265,A_262,B_264] :
      ( r2_hidden(k4_tarski(A_262,B_261),B_264)
      | ~ r1_tarski(k2_zfmisc_1(C_263,D_265),B_264)
      | ~ r2_hidden(B_261,D_265)
      | ~ r2_hidden(A_262,C_263) ) ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_1085,plain,(
    ! [A_266,B_267] :
      ( r2_hidden(k4_tarski(A_266,B_267),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_267,'#skF_10')
      | ~ r2_hidden(A_266,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_1069])).

tff(c_44,plain,(
    ! [A_46,C_48,B_47,D_49] :
      ( r2_hidden(A_46,C_48)
      | ~ r2_hidden(k4_tarski(A_46,B_47),k2_zfmisc_1(C_48,D_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1109,plain,(
    ! [A_266,B_267] :
      ( r2_hidden(A_266,'#skF_11')
      | ~ r2_hidden(B_267,'#skF_10')
      | ~ r2_hidden(A_266,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1085,c_44])).

tff(c_1113,plain,(
    ! [B_268] : ~ r2_hidden(B_268,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1109])).

tff(c_1180,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_858,c_1113])).

tff(c_54,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_54])).

tff(c_1271,plain,(
    ! [A_274] :
      ( r2_hidden(A_274,'#skF_11')
      | ~ r2_hidden(A_274,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_1109])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1338,plain,(
    ! [A_279] :
      ( r1_tarski(A_279,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_279,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1271,c_4])).

tff(c_1346,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_1338])).

tff(c_1351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_80,c_1346])).

tff(c_1352,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_38,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_4'(A_12,B_13,C_14),A_12)
      | r2_hidden('#skF_6'(A_12,B_13,C_14),C_14)
      | k2_zfmisc_1(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1375,plain,(
    ! [A_291,B_292,C_293] :
      ( ~ r1_xboole_0(A_291,B_292)
      | ~ r2_hidden(C_293,B_292)
      | ~ r2_hidden(C_293,A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1379,plain,(
    ! [C_294,A_295] :
      ( ~ r2_hidden(C_294,k1_xboole_0)
      | ~ r2_hidden(C_294,A_295) ) ),
    inference(resolution,[status(thm)],[c_14,c_1375])).

tff(c_1420,plain,(
    ! [B_302,A_303] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_302),A_303)
      | r1_tarski(k1_xboole_0,B_302) ) ),
    inference(resolution,[status(thm)],[c_6,c_1379])).

tff(c_1425,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1420])).

tff(c_1517,plain,(
    ! [A_337,B_338,D_339] :
      ( r2_hidden('#skF_8'(A_337,B_338,k2_zfmisc_1(A_337,B_338),D_339),B_338)
      | ~ r2_hidden(D_339,k2_zfmisc_1(A_337,B_338)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1532,plain,(
    ! [B_51,D_339] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_51,k1_xboole_0,D_339),B_51)
      | ~ r2_hidden(D_339,k2_zfmisc_1(k1_xboole_0,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1517])).

tff(c_1555,plain,(
    ! [B_342,D_343] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_342,k1_xboole_0,D_343),B_342)
      | ~ r2_hidden(D_343,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1532])).

tff(c_2054,plain,(
    ! [B_432,D_433,B_434] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_432,k1_xboole_0,D_433),B_434)
      | ~ r1_tarski(B_432,B_434)
      | ~ r2_hidden(D_433,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1555,c_2])).

tff(c_1378,plain,(
    ! [C_293,A_11] :
      ( ~ r2_hidden(C_293,k1_xboole_0)
      | ~ r2_hidden(C_293,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_1375])).

tff(c_1526,plain,(
    ! [A_337,D_339,A_11] :
      ( ~ r2_hidden('#skF_8'(A_337,k1_xboole_0,k2_zfmisc_1(A_337,k1_xboole_0),D_339),A_11)
      | ~ r2_hidden(D_339,k2_zfmisc_1(A_337,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1517,c_1378])).

tff(c_1537,plain,(
    ! [A_337,D_339,A_11] :
      ( ~ r2_hidden('#skF_8'(A_337,k1_xboole_0,k1_xboole_0,D_339),A_11)
      | ~ r2_hidden(D_339,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_1526])).

tff(c_2062,plain,(
    ! [B_434,D_433] :
      ( ~ r1_tarski(k1_xboole_0,B_434)
      | ~ r2_hidden(D_433,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2054,c_1537])).

tff(c_2083,plain,(
    ! [D_435] : ~ r2_hidden(D_435,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_2062])).

tff(c_2134,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13,k1_xboole_0),A_12)
      | k2_zfmisc_1(A_12,B_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_2083])).

tff(c_1444,plain,(
    ! [A_318,B_319,C_320,D_321] :
      ( r2_hidden(k4_tarski(A_318,B_319),k2_zfmisc_1(C_320,D_321))
      | ~ r2_hidden(B_319,D_321)
      | ~ r2_hidden(A_318,C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2500,plain,(
    ! [B_504,D_503,C_501,A_500,B_502] :
      ( r2_hidden(k4_tarski(A_500,B_502),B_504)
      | ~ r1_tarski(k2_zfmisc_1(C_501,D_503),B_504)
      | ~ r2_hidden(B_502,D_503)
      | ~ r2_hidden(A_500,C_501) ) ),
    inference(resolution,[status(thm)],[c_1444,c_2])).

tff(c_2524,plain,(
    ! [A_505,B_506] :
      ( r2_hidden(k4_tarski(A_505,B_506),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_506,'#skF_10')
      | ~ r2_hidden(A_505,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_2500])).

tff(c_42,plain,(
    ! [B_47,D_49,A_46,C_48] :
      ( r2_hidden(B_47,D_49)
      | ~ r2_hidden(k4_tarski(A_46,B_47),k2_zfmisc_1(C_48,D_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2545,plain,(
    ! [B_506,A_505] :
      ( r2_hidden(B_506,'#skF_12')
      | ~ r2_hidden(B_506,'#skF_10')
      | ~ r2_hidden(A_505,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2524,c_42])).

tff(c_2549,plain,(
    ! [A_507] : ~ r2_hidden(A_507,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2545])).

tff(c_2626,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_9',B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2134,c_2549])).

tff(c_2802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2626,c_54])).

tff(c_2804,plain,(
    ! [B_518] :
      ( r2_hidden(B_518,'#skF_12')
      | ~ r2_hidden(B_518,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_2545])).

tff(c_2937,plain,(
    ! [B_523] :
      ( r2_hidden('#skF_1'('#skF_10',B_523),'#skF_12')
      | r1_tarski('#skF_10',B_523) ) ),
    inference(resolution,[status(thm)],[c_6,c_2804])).

tff(c_2950,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_2937,c_4])).

tff(c_2958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1352,c_1352,c_2950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:14:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.98  
% 5.00/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 5.00/1.99  
% 5.00/1.99  %Foreground sorts:
% 5.00/1.99  
% 5.00/1.99  
% 5.00/1.99  %Background operators:
% 5.00/1.99  
% 5.00/1.99  
% 5.00/1.99  %Foreground operators:
% 5.00/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.99  tff('#skF_11', type, '#skF_11': $i).
% 5.00/1.99  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.00/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.00/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.00/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.99  tff('#skF_10', type, '#skF_10': $i).
% 5.00/1.99  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.00/1.99  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.00/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.00/1.99  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.00/1.99  tff('#skF_9', type, '#skF_9': $i).
% 5.00/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.00/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.00/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.00/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.00/1.99  tff('#skF_12', type, '#skF_12': $i).
% 5.00/1.99  
% 5.00/2.00  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.00/2.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.00/2.00  tff(f_64, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.00/2.00  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.00/2.00  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.00/2.00  tff(f_76, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.00/2.00  tff(f_70, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.00/2.00  tff(c_52, plain, (~r1_tarski('#skF_10', '#skF_12') | ~r1_tarski('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.00/2.00  tff(c_80, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_52])).
% 5.00/2.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.00/2.00  tff(c_36, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_5'(A_12, B_13, C_14), B_13) | r2_hidden('#skF_6'(A_12, B_13, C_14), C_14) | k2_zfmisc_1(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/2.00  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.00/2.00  tff(c_112, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, B_70) | ~r2_hidden(C_71, A_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.00/2.00  tff(c_123, plain, (![C_76, A_77]: (~r2_hidden(C_76, k1_xboole_0) | ~r2_hidden(C_76, A_77))), inference(resolution, [status(thm)], [c_14, c_112])).
% 5.00/2.00  tff(c_182, plain, (![B_97, A_98]: (~r2_hidden('#skF_1'(k1_xboole_0, B_97), A_98) | r1_tarski(k1_xboole_0, B_97))), inference(resolution, [status(thm)], [c_6, c_123])).
% 5.00/2.00  tff(c_187, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_182])).
% 5.00/2.00  tff(c_50, plain, (![B_51]: (k2_zfmisc_1(k1_xboole_0, B_51)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.00/2.00  tff(c_203, plain, (![A_103, B_104, D_105]: (r2_hidden('#skF_8'(A_103, B_104, k2_zfmisc_1(A_103, B_104), D_105), B_104) | ~r2_hidden(D_105, k2_zfmisc_1(A_103, B_104)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/2.00  tff(c_216, plain, (![B_51, D_105]: (r2_hidden('#skF_8'(k1_xboole_0, B_51, k1_xboole_0, D_105), B_51) | ~r2_hidden(D_105, k2_zfmisc_1(k1_xboole_0, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_203])).
% 5.00/2.00  tff(c_235, plain, (![B_108, D_109]: (r2_hidden('#skF_8'(k1_xboole_0, B_108, k1_xboole_0, D_109), B_108) | ~r2_hidden(D_109, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_216])).
% 5.00/2.00  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.00/2.00  tff(c_775, plain, (![B_207, D_208, B_209]: (r2_hidden('#skF_8'(k1_xboole_0, B_207, k1_xboole_0, D_208), B_209) | ~r1_tarski(B_207, B_209) | ~r2_hidden(D_208, k1_xboole_0))), inference(resolution, [status(thm)], [c_235, c_2])).
% 5.00/2.00  tff(c_48, plain, (![A_50]: (k2_zfmisc_1(A_50, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.00/2.00  tff(c_115, plain, (![C_71, A_11]: (~r2_hidden(C_71, k1_xboole_0) | ~r2_hidden(C_71, A_11))), inference(resolution, [status(thm)], [c_14, c_112])).
% 5.00/2.00  tff(c_208, plain, (![A_103, D_105, A_11]: (~r2_hidden('#skF_8'(A_103, k1_xboole_0, k2_zfmisc_1(A_103, k1_xboole_0), D_105), A_11) | ~r2_hidden(D_105, k2_zfmisc_1(A_103, k1_xboole_0)))), inference(resolution, [status(thm)], [c_203, c_115])).
% 5.00/2.00  tff(c_219, plain, (![A_103, D_105, A_11]: (~r2_hidden('#skF_8'(A_103, k1_xboole_0, k1_xboole_0, D_105), A_11) | ~r2_hidden(D_105, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_208])).
% 5.00/2.00  tff(c_785, plain, (![B_209, D_208]: (~r1_tarski(k1_xboole_0, B_209) | ~r2_hidden(D_208, k1_xboole_0))), inference(resolution, [status(thm)], [c_775, c_219])).
% 5.00/2.00  tff(c_804, plain, (![D_210]: (~r2_hidden(D_210, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_785])).
% 5.00/2.00  tff(c_858, plain, (![A_12, B_13]: (r2_hidden('#skF_5'(A_12, B_13, k1_xboole_0), B_13) | k2_zfmisc_1(A_12, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_804])).
% 5.00/2.00  tff(c_56, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.00/2.00  tff(c_164, plain, (![A_93, B_94, C_95, D_96]: (r2_hidden(k4_tarski(A_93, B_94), k2_zfmisc_1(C_95, D_96)) | ~r2_hidden(B_94, D_96) | ~r2_hidden(A_93, C_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.00/2.00  tff(c_1069, plain, (![B_261, C_263, D_265, A_262, B_264]: (r2_hidden(k4_tarski(A_262, B_261), B_264) | ~r1_tarski(k2_zfmisc_1(C_263, D_265), B_264) | ~r2_hidden(B_261, D_265) | ~r2_hidden(A_262, C_263))), inference(resolution, [status(thm)], [c_164, c_2])).
% 5.00/2.00  tff(c_1085, plain, (![A_266, B_267]: (r2_hidden(k4_tarski(A_266, B_267), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_267, '#skF_10') | ~r2_hidden(A_266, '#skF_9'))), inference(resolution, [status(thm)], [c_56, c_1069])).
% 5.00/2.00  tff(c_44, plain, (![A_46, C_48, B_47, D_49]: (r2_hidden(A_46, C_48) | ~r2_hidden(k4_tarski(A_46, B_47), k2_zfmisc_1(C_48, D_49)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.00/2.00  tff(c_1109, plain, (![A_266, B_267]: (r2_hidden(A_266, '#skF_11') | ~r2_hidden(B_267, '#skF_10') | ~r2_hidden(A_266, '#skF_9'))), inference(resolution, [status(thm)], [c_1085, c_44])).
% 5.00/2.00  tff(c_1113, plain, (![B_268]: (~r2_hidden(B_268, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1109])).
% 5.00/2.00  tff(c_1180, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_858, c_1113])).
% 5.00/2.00  tff(c_54, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.00/2.00  tff(c_1269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1180, c_54])).
% 5.00/2.00  tff(c_1271, plain, (![A_274]: (r2_hidden(A_274, '#skF_11') | ~r2_hidden(A_274, '#skF_9'))), inference(splitRight, [status(thm)], [c_1109])).
% 5.00/2.00  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.00/2.00  tff(c_1338, plain, (![A_279]: (r1_tarski(A_279, '#skF_11') | ~r2_hidden('#skF_1'(A_279, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_1271, c_4])).
% 5.00/2.00  tff(c_1346, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_1338])).
% 5.00/2.00  tff(c_1351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_80, c_1346])).
% 5.00/2.00  tff(c_1352, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_52])).
% 5.00/2.00  tff(c_38, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_4'(A_12, B_13, C_14), A_12) | r2_hidden('#skF_6'(A_12, B_13, C_14), C_14) | k2_zfmisc_1(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/2.00  tff(c_1375, plain, (![A_291, B_292, C_293]: (~r1_xboole_0(A_291, B_292) | ~r2_hidden(C_293, B_292) | ~r2_hidden(C_293, A_291))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.00/2.00  tff(c_1379, plain, (![C_294, A_295]: (~r2_hidden(C_294, k1_xboole_0) | ~r2_hidden(C_294, A_295))), inference(resolution, [status(thm)], [c_14, c_1375])).
% 5.00/2.00  tff(c_1420, plain, (![B_302, A_303]: (~r2_hidden('#skF_1'(k1_xboole_0, B_302), A_303) | r1_tarski(k1_xboole_0, B_302))), inference(resolution, [status(thm)], [c_6, c_1379])).
% 5.00/2.00  tff(c_1425, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_1420])).
% 5.00/2.00  tff(c_1517, plain, (![A_337, B_338, D_339]: (r2_hidden('#skF_8'(A_337, B_338, k2_zfmisc_1(A_337, B_338), D_339), B_338) | ~r2_hidden(D_339, k2_zfmisc_1(A_337, B_338)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/2.00  tff(c_1532, plain, (![B_51, D_339]: (r2_hidden('#skF_8'(k1_xboole_0, B_51, k1_xboole_0, D_339), B_51) | ~r2_hidden(D_339, k2_zfmisc_1(k1_xboole_0, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1517])).
% 5.00/2.00  tff(c_1555, plain, (![B_342, D_343]: (r2_hidden('#skF_8'(k1_xboole_0, B_342, k1_xboole_0, D_343), B_342) | ~r2_hidden(D_343, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1532])).
% 5.00/2.00  tff(c_2054, plain, (![B_432, D_433, B_434]: (r2_hidden('#skF_8'(k1_xboole_0, B_432, k1_xboole_0, D_433), B_434) | ~r1_tarski(B_432, B_434) | ~r2_hidden(D_433, k1_xboole_0))), inference(resolution, [status(thm)], [c_1555, c_2])).
% 5.00/2.00  tff(c_1378, plain, (![C_293, A_11]: (~r2_hidden(C_293, k1_xboole_0) | ~r2_hidden(C_293, A_11))), inference(resolution, [status(thm)], [c_14, c_1375])).
% 5.00/2.00  tff(c_1526, plain, (![A_337, D_339, A_11]: (~r2_hidden('#skF_8'(A_337, k1_xboole_0, k2_zfmisc_1(A_337, k1_xboole_0), D_339), A_11) | ~r2_hidden(D_339, k2_zfmisc_1(A_337, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1517, c_1378])).
% 5.00/2.00  tff(c_1537, plain, (![A_337, D_339, A_11]: (~r2_hidden('#skF_8'(A_337, k1_xboole_0, k1_xboole_0, D_339), A_11) | ~r2_hidden(D_339, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_1526])).
% 5.00/2.00  tff(c_2062, plain, (![B_434, D_433]: (~r1_tarski(k1_xboole_0, B_434) | ~r2_hidden(D_433, k1_xboole_0))), inference(resolution, [status(thm)], [c_2054, c_1537])).
% 5.00/2.00  tff(c_2083, plain, (![D_435]: (~r2_hidden(D_435, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_2062])).
% 5.00/2.00  tff(c_2134, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13, k1_xboole_0), A_12) | k2_zfmisc_1(A_12, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2083])).
% 5.00/2.00  tff(c_1444, plain, (![A_318, B_319, C_320, D_321]: (r2_hidden(k4_tarski(A_318, B_319), k2_zfmisc_1(C_320, D_321)) | ~r2_hidden(B_319, D_321) | ~r2_hidden(A_318, C_320))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.00/2.00  tff(c_2500, plain, (![B_504, D_503, C_501, A_500, B_502]: (r2_hidden(k4_tarski(A_500, B_502), B_504) | ~r1_tarski(k2_zfmisc_1(C_501, D_503), B_504) | ~r2_hidden(B_502, D_503) | ~r2_hidden(A_500, C_501))), inference(resolution, [status(thm)], [c_1444, c_2])).
% 5.00/2.00  tff(c_2524, plain, (![A_505, B_506]: (r2_hidden(k4_tarski(A_505, B_506), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_506, '#skF_10') | ~r2_hidden(A_505, '#skF_9'))), inference(resolution, [status(thm)], [c_56, c_2500])).
% 5.00/2.00  tff(c_42, plain, (![B_47, D_49, A_46, C_48]: (r2_hidden(B_47, D_49) | ~r2_hidden(k4_tarski(A_46, B_47), k2_zfmisc_1(C_48, D_49)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.00/2.00  tff(c_2545, plain, (![B_506, A_505]: (r2_hidden(B_506, '#skF_12') | ~r2_hidden(B_506, '#skF_10') | ~r2_hidden(A_505, '#skF_9'))), inference(resolution, [status(thm)], [c_2524, c_42])).
% 5.00/2.00  tff(c_2549, plain, (![A_507]: (~r2_hidden(A_507, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2545])).
% 5.00/2.00  tff(c_2626, plain, (![B_13]: (k2_zfmisc_1('#skF_9', B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2134, c_2549])).
% 5.00/2.00  tff(c_2802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2626, c_54])).
% 5.00/2.00  tff(c_2804, plain, (![B_518]: (r2_hidden(B_518, '#skF_12') | ~r2_hidden(B_518, '#skF_10'))), inference(splitRight, [status(thm)], [c_2545])).
% 5.00/2.00  tff(c_2937, plain, (![B_523]: (r2_hidden('#skF_1'('#skF_10', B_523), '#skF_12') | r1_tarski('#skF_10', B_523))), inference(resolution, [status(thm)], [c_6, c_2804])).
% 5.00/2.00  tff(c_2950, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_2937, c_4])).
% 5.00/2.00  tff(c_2958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1352, c_1352, c_2950])).
% 5.00/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/2.00  
% 5.00/2.00  Inference rules
% 5.00/2.00  ----------------------
% 5.00/2.00  #Ref     : 0
% 5.00/2.00  #Sup     : 718
% 5.00/2.00  #Fact    : 0
% 5.00/2.00  #Define  : 0
% 5.00/2.00  #Split   : 9
% 5.00/2.00  #Chain   : 0
% 5.00/2.00  #Close   : 0
% 5.00/2.00  
% 5.00/2.00  Ordering : KBO
% 5.00/2.00  
% 5.00/2.00  Simplification rules
% 5.00/2.00  ----------------------
% 5.00/2.00  #Subsume      : 286
% 5.00/2.00  #Demod        : 106
% 5.00/2.00  #Tautology    : 63
% 5.00/2.00  #SimpNegUnit  : 27
% 5.00/2.00  #BackRed      : 11
% 5.00/2.00  
% 5.00/2.00  #Partial instantiations: 0
% 5.00/2.00  #Strategies tried      : 1
% 5.00/2.00  
% 5.00/2.00  Timing (in seconds)
% 5.00/2.00  ----------------------
% 5.00/2.01  Preprocessing        : 0.31
% 5.00/2.01  Parsing              : 0.16
% 5.00/2.01  CNF conversion       : 0.03
% 5.00/2.01  Main loop            : 0.91
% 5.00/2.01  Inferencing          : 0.33
% 5.00/2.01  Reduction            : 0.23
% 5.00/2.01  Demodulation         : 0.15
% 5.00/2.01  BG Simplification    : 0.04
% 5.00/2.01  Subsumption          : 0.24
% 5.00/2.01  Abstraction          : 0.04
% 5.00/2.01  MUC search           : 0.00
% 5.00/2.01  Cooper               : 0.00
% 5.00/2.01  Total                : 1.25
% 5.00/2.01  Index Insertion      : 0.00
% 5.00/2.01  Index Deletion       : 0.00
% 5.00/2.01  Index Matching       : 0.00
% 5.00/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
