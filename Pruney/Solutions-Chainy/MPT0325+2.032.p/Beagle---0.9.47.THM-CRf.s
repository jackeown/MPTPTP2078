%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 215 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 422 expanded)
%              Number of equality atoms :   28 (  78 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_89,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_10','#skF_12')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1167,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden('#skF_5'(A_176,B_177,C_178),B_177)
      | r2_hidden('#skF_6'(A_176,B_177,C_178),C_178)
      | k2_zfmisc_1(A_176,B_177) = C_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [B_61,A_62] :
      ( r1_xboole_0(B_61,A_62)
      | ~ r1_xboole_0(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_18,c_92])).

tff(c_109,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_156,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,(
    ! [B_70,C_76] :
      ( ~ r1_xboole_0(k1_xboole_0,B_70)
      | ~ r2_hidden(C_76,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_156])).

tff(c_165,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_159])).

tff(c_1248,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_5'(A_176,B_177,k1_xboole_0),B_177)
      | k2_zfmisc_1(A_176,B_177) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1167,c_165])).

tff(c_60,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_259,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_hidden(k4_tarski(A_100,B_101),k2_zfmisc_1(C_102,D_103))
      | ~ r2_hidden(B_101,D_103)
      | ~ r2_hidden(A_100,C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2741,plain,(
    ! [B_293,A_294,C_291,D_292,B_295] :
      ( r2_hidden(k4_tarski(A_294,B_293),B_295)
      | ~ r1_tarski(k2_zfmisc_1(C_291,D_292),B_295)
      | ~ r2_hidden(B_293,D_292)
      | ~ r2_hidden(A_294,C_291) ) ),
    inference(resolution,[status(thm)],[c_259,c_2])).

tff(c_2908,plain,(
    ! [A_305,B_306] :
      ( r2_hidden(k4_tarski(A_305,B_306),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_306,'#skF_10')
      | ~ r2_hidden(A_305,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_2741])).

tff(c_48,plain,(
    ! [A_51,C_53,B_52,D_54] :
      ( r2_hidden(A_51,C_53)
      | ~ r2_hidden(k4_tarski(A_51,B_52),k2_zfmisc_1(C_53,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2923,plain,(
    ! [A_305,B_306] :
      ( r2_hidden(A_305,'#skF_11')
      | ~ r2_hidden(B_306,'#skF_10')
      | ~ r2_hidden(A_305,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2908,c_48])).

tff(c_2927,plain,(
    ! [B_307] : ~ r2_hidden(B_307,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2923])).

tff(c_2972,plain,(
    ! [A_176] : k2_zfmisc_1(A_176,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1248,c_2927])).

tff(c_58,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2972,c_58])).

tff(c_3009,plain,(
    ! [A_309] :
      ( r2_hidden(A_309,'#skF_11')
      | ~ r2_hidden(A_309,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2923])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3022,plain,(
    ! [A_310] :
      ( r1_tarski(A_310,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_310,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3009,c_4])).

tff(c_3030,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_3022])).

tff(c_3035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_91,c_3030])).

tff(c_3036,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,(
    ! [A_55] : k2_zfmisc_1(A_55,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3058,plain,(
    ! [A_316,B_317] : k4_xboole_0(A_316,k4_xboole_0(A_316,B_317)) = k3_xboole_0(A_316,B_317) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3068,plain,(
    ! [B_317] : k3_xboole_0(k1_xboole_0,B_317) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3058,c_16])).

tff(c_3038,plain,(
    ! [B_311,A_312] :
      ( r1_xboole_0(B_311,A_312)
      | ~ r1_xboole_0(A_312,B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3041,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_18,c_3038])).

tff(c_4115,plain,(
    ! [A_438,B_439,C_440] :
      ( r2_hidden('#skF_5'(A_438,B_439,C_440),B_439)
      | r2_hidden('#skF_6'(A_438,B_439,C_440),C_440)
      | k2_zfmisc_1(A_438,B_439) = C_440 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5962,plain,(
    ! [A_561,B_562,A_563,C_564] :
      ( ~ r1_xboole_0(A_561,B_562)
      | r2_hidden('#skF_6'(A_563,k3_xboole_0(A_561,B_562),C_564),C_564)
      | k2_zfmisc_1(A_563,k3_xboole_0(A_561,B_562)) = C_564 ) ),
    inference(resolution,[status(thm)],[c_4115,c_12])).

tff(c_6017,plain,(
    ! [B_317,A_563,C_564] :
      ( ~ r1_xboole_0(k1_xboole_0,B_317)
      | r2_hidden('#skF_6'(A_563,k1_xboole_0,C_564),C_564)
      | k2_zfmisc_1(A_563,k3_xboole_0(k1_xboole_0,B_317)) = C_564 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3068,c_5962])).

tff(c_6034,plain,(
    ! [A_563,C_564] :
      ( r2_hidden('#skF_6'(A_563,k1_xboole_0,C_564),C_564)
      | k1_xboole_0 = C_564 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3068,c_3041,c_6017])).

tff(c_3205,plain,(
    ! [A_350,B_351,C_352,D_353] :
      ( r2_hidden(k4_tarski(A_350,B_351),k2_zfmisc_1(C_352,D_353))
      | ~ r2_hidden(B_351,D_353)
      | ~ r2_hidden(A_350,C_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5658,plain,(
    ! [C_540,A_543,B_544,D_541,B_542] :
      ( r2_hidden(k4_tarski(A_543,B_542),B_544)
      | ~ r1_tarski(k2_zfmisc_1(C_540,D_541),B_544)
      | ~ r2_hidden(B_542,D_541)
      | ~ r2_hidden(A_543,C_540) ) ),
    inference(resolution,[status(thm)],[c_3205,c_2])).

tff(c_5854,plain,(
    ! [A_555,B_556] :
      ( r2_hidden(k4_tarski(A_555,B_556),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_556,'#skF_10')
      | ~ r2_hidden(A_555,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_5658])).

tff(c_46,plain,(
    ! [B_52,D_54,A_51,C_53] :
      ( r2_hidden(B_52,D_54)
      | ~ r2_hidden(k4_tarski(A_51,B_52),k2_zfmisc_1(C_53,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5870,plain,(
    ! [B_556,A_555] :
      ( r2_hidden(B_556,'#skF_12')
      | ~ r2_hidden(B_556,'#skF_10')
      | ~ r2_hidden(A_555,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5854,c_46])).

tff(c_6171,plain,(
    ! [A_570] : ~ r2_hidden(A_570,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5870])).

tff(c_6224,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6034,c_6171])).

tff(c_3779,plain,(
    ! [A_427,B_428,C_429] :
      ( r2_hidden('#skF_4'(A_427,B_428,C_429),A_427)
      | r2_hidden('#skF_6'(A_427,B_428,C_429),C_429)
      | k2_zfmisc_1(A_427,B_428) = C_429 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3094,plain,(
    ! [A_319,B_320,C_321] :
      ( ~ r1_xboole_0(A_319,B_320)
      | ~ r2_hidden(C_321,k3_xboole_0(A_319,B_320)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3097,plain,(
    ! [B_317,C_321] :
      ( ~ r1_xboole_0(k1_xboole_0,B_317)
      | ~ r2_hidden(C_321,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3068,c_3094])).

tff(c_3099,plain,(
    ! [C_321] : ~ r2_hidden(C_321,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3041,c_3097])).

tff(c_3861,plain,(
    ! [A_427,B_428] :
      ( r2_hidden('#skF_4'(A_427,B_428,k1_xboole_0),A_427)
      | k2_zfmisc_1(A_427,B_428) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3779,c_3099])).

tff(c_6228,plain,(
    ! [B_428] : k2_zfmisc_1('#skF_9',B_428) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3861,c_6171])).

tff(c_6355,plain,(
    ! [B_428] : k2_zfmisc_1('#skF_9',B_428) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6224,c_6228])).

tff(c_6277,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6224,c_58])).

tff(c_6359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6355,c_6277])).

tff(c_6361,plain,(
    ! [B_578] :
      ( r2_hidden(B_578,'#skF_12')
      | ~ r2_hidden(B_578,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_5870])).

tff(c_6562,plain,(
    ! [B_584] :
      ( r2_hidden('#skF_1'('#skF_10',B_584),'#skF_12')
      | r1_tarski('#skF_10',B_584) ) ),
    inference(resolution,[status(thm)],[c_6,c_6361])).

tff(c_6568,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_6562,c_4])).

tff(c_6573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3036,c_3036,c_6568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.16  
% 5.89/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 5.89/2.16  
% 5.89/2.16  %Foreground sorts:
% 5.89/2.16  
% 5.89/2.16  
% 5.89/2.16  %Background operators:
% 5.89/2.16  
% 5.89/2.16  
% 5.89/2.16  %Foreground operators:
% 5.89/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/2.16  tff('#skF_11', type, '#skF_11': $i).
% 5.89/2.16  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.89/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.89/2.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.89/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.89/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.16  tff('#skF_10', type, '#skF_10': $i).
% 5.89/2.16  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.89/2.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.89/2.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.89/2.16  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.89/2.16  tff('#skF_9', type, '#skF_9': $i).
% 5.89/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.89/2.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.89/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.89/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.89/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.89/2.16  tff('#skF_12', type, '#skF_12': $i).
% 5.89/2.16  
% 5.89/2.17  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.89/2.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.89/2.17  tff(f_68, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.89/2.17  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.89/2.17  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.89/2.17  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.89/2.18  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.89/2.18  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.89/2.18  tff(f_74, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.89/2.18  tff(f_80, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.89/2.18  tff(c_56, plain, (~r1_tarski('#skF_10', '#skF_12') | ~r1_tarski('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.89/2.18  tff(c_91, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_56])).
% 5.89/2.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.18  tff(c_1167, plain, (![A_176, B_177, C_178]: (r2_hidden('#skF_5'(A_176, B_177, C_178), B_177) | r2_hidden('#skF_6'(A_176, B_177, C_178), C_178) | k2_zfmisc_1(A_176, B_177)=C_178)), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.89/2.18  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.18  tff(c_92, plain, (![B_61, A_62]: (r1_xboole_0(B_61, A_62) | ~r1_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.89/2.18  tff(c_95, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_18, c_92])).
% 5.89/2.18  tff(c_109, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.89/2.18  tff(c_16, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.89/2.18  tff(c_119, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_16])).
% 5.89/2.18  tff(c_156, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.89/2.18  tff(c_159, plain, (![B_70, C_76]: (~r1_xboole_0(k1_xboole_0, B_70) | ~r2_hidden(C_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119, c_156])).
% 5.89/2.18  tff(c_165, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_159])).
% 5.89/2.18  tff(c_1248, plain, (![A_176, B_177]: (r2_hidden('#skF_5'(A_176, B_177, k1_xboole_0), B_177) | k2_zfmisc_1(A_176, B_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1167, c_165])).
% 5.89/2.18  tff(c_60, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.89/2.18  tff(c_259, plain, (![A_100, B_101, C_102, D_103]: (r2_hidden(k4_tarski(A_100, B_101), k2_zfmisc_1(C_102, D_103)) | ~r2_hidden(B_101, D_103) | ~r2_hidden(A_100, C_102))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.89/2.18  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.18  tff(c_2741, plain, (![B_293, A_294, C_291, D_292, B_295]: (r2_hidden(k4_tarski(A_294, B_293), B_295) | ~r1_tarski(k2_zfmisc_1(C_291, D_292), B_295) | ~r2_hidden(B_293, D_292) | ~r2_hidden(A_294, C_291))), inference(resolution, [status(thm)], [c_259, c_2])).
% 5.89/2.18  tff(c_2908, plain, (![A_305, B_306]: (r2_hidden(k4_tarski(A_305, B_306), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_306, '#skF_10') | ~r2_hidden(A_305, '#skF_9'))), inference(resolution, [status(thm)], [c_60, c_2741])).
% 5.89/2.18  tff(c_48, plain, (![A_51, C_53, B_52, D_54]: (r2_hidden(A_51, C_53) | ~r2_hidden(k4_tarski(A_51, B_52), k2_zfmisc_1(C_53, D_54)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.89/2.18  tff(c_2923, plain, (![A_305, B_306]: (r2_hidden(A_305, '#skF_11') | ~r2_hidden(B_306, '#skF_10') | ~r2_hidden(A_305, '#skF_9'))), inference(resolution, [status(thm)], [c_2908, c_48])).
% 5.89/2.18  tff(c_2927, plain, (![B_307]: (~r2_hidden(B_307, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2923])).
% 5.89/2.18  tff(c_2972, plain, (![A_176]: (k2_zfmisc_1(A_176, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1248, c_2927])).
% 5.89/2.18  tff(c_58, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.89/2.18  tff(c_3007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2972, c_58])).
% 5.89/2.18  tff(c_3009, plain, (![A_309]: (r2_hidden(A_309, '#skF_11') | ~r2_hidden(A_309, '#skF_9'))), inference(splitRight, [status(thm)], [c_2923])).
% 5.89/2.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.18  tff(c_3022, plain, (![A_310]: (r1_tarski(A_310, '#skF_11') | ~r2_hidden('#skF_1'(A_310, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_3009, c_4])).
% 5.89/2.18  tff(c_3030, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_3022])).
% 5.89/2.18  tff(c_3035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_91, c_3030])).
% 5.89/2.18  tff(c_3036, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_56])).
% 5.89/2.18  tff(c_52, plain, (![A_55]: (k2_zfmisc_1(A_55, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.89/2.18  tff(c_3058, plain, (![A_316, B_317]: (k4_xboole_0(A_316, k4_xboole_0(A_316, B_317))=k3_xboole_0(A_316, B_317))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.89/2.18  tff(c_3068, plain, (![B_317]: (k3_xboole_0(k1_xboole_0, B_317)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3058, c_16])).
% 5.89/2.18  tff(c_3038, plain, (![B_311, A_312]: (r1_xboole_0(B_311, A_312) | ~r1_xboole_0(A_312, B_311))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.89/2.18  tff(c_3041, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_18, c_3038])).
% 5.89/2.18  tff(c_4115, plain, (![A_438, B_439, C_440]: (r2_hidden('#skF_5'(A_438, B_439, C_440), B_439) | r2_hidden('#skF_6'(A_438, B_439, C_440), C_440) | k2_zfmisc_1(A_438, B_439)=C_440)), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.89/2.18  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.89/2.18  tff(c_5962, plain, (![A_561, B_562, A_563, C_564]: (~r1_xboole_0(A_561, B_562) | r2_hidden('#skF_6'(A_563, k3_xboole_0(A_561, B_562), C_564), C_564) | k2_zfmisc_1(A_563, k3_xboole_0(A_561, B_562))=C_564)), inference(resolution, [status(thm)], [c_4115, c_12])).
% 5.89/2.18  tff(c_6017, plain, (![B_317, A_563, C_564]: (~r1_xboole_0(k1_xboole_0, B_317) | r2_hidden('#skF_6'(A_563, k1_xboole_0, C_564), C_564) | k2_zfmisc_1(A_563, k3_xboole_0(k1_xboole_0, B_317))=C_564)), inference(superposition, [status(thm), theory('equality')], [c_3068, c_5962])).
% 5.89/2.18  tff(c_6034, plain, (![A_563, C_564]: (r2_hidden('#skF_6'(A_563, k1_xboole_0, C_564), C_564) | k1_xboole_0=C_564)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3068, c_3041, c_6017])).
% 5.89/2.18  tff(c_3205, plain, (![A_350, B_351, C_352, D_353]: (r2_hidden(k4_tarski(A_350, B_351), k2_zfmisc_1(C_352, D_353)) | ~r2_hidden(B_351, D_353) | ~r2_hidden(A_350, C_352))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.89/2.18  tff(c_5658, plain, (![C_540, A_543, B_544, D_541, B_542]: (r2_hidden(k4_tarski(A_543, B_542), B_544) | ~r1_tarski(k2_zfmisc_1(C_540, D_541), B_544) | ~r2_hidden(B_542, D_541) | ~r2_hidden(A_543, C_540))), inference(resolution, [status(thm)], [c_3205, c_2])).
% 5.89/2.18  tff(c_5854, plain, (![A_555, B_556]: (r2_hidden(k4_tarski(A_555, B_556), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_556, '#skF_10') | ~r2_hidden(A_555, '#skF_9'))), inference(resolution, [status(thm)], [c_60, c_5658])).
% 5.89/2.18  tff(c_46, plain, (![B_52, D_54, A_51, C_53]: (r2_hidden(B_52, D_54) | ~r2_hidden(k4_tarski(A_51, B_52), k2_zfmisc_1(C_53, D_54)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.89/2.18  tff(c_5870, plain, (![B_556, A_555]: (r2_hidden(B_556, '#skF_12') | ~r2_hidden(B_556, '#skF_10') | ~r2_hidden(A_555, '#skF_9'))), inference(resolution, [status(thm)], [c_5854, c_46])).
% 5.89/2.18  tff(c_6171, plain, (![A_570]: (~r2_hidden(A_570, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5870])).
% 5.89/2.18  tff(c_6224, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6034, c_6171])).
% 5.89/2.18  tff(c_3779, plain, (![A_427, B_428, C_429]: (r2_hidden('#skF_4'(A_427, B_428, C_429), A_427) | r2_hidden('#skF_6'(A_427, B_428, C_429), C_429) | k2_zfmisc_1(A_427, B_428)=C_429)), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.89/2.18  tff(c_3094, plain, (![A_319, B_320, C_321]: (~r1_xboole_0(A_319, B_320) | ~r2_hidden(C_321, k3_xboole_0(A_319, B_320)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.89/2.18  tff(c_3097, plain, (![B_317, C_321]: (~r1_xboole_0(k1_xboole_0, B_317) | ~r2_hidden(C_321, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3068, c_3094])).
% 5.89/2.18  tff(c_3099, plain, (![C_321]: (~r2_hidden(C_321, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3041, c_3097])).
% 5.89/2.18  tff(c_3861, plain, (![A_427, B_428]: (r2_hidden('#skF_4'(A_427, B_428, k1_xboole_0), A_427) | k2_zfmisc_1(A_427, B_428)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3779, c_3099])).
% 5.89/2.18  tff(c_6228, plain, (![B_428]: (k2_zfmisc_1('#skF_9', B_428)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3861, c_6171])).
% 5.89/2.18  tff(c_6355, plain, (![B_428]: (k2_zfmisc_1('#skF_9', B_428)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6224, c_6228])).
% 5.89/2.18  tff(c_6277, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6224, c_58])).
% 5.89/2.18  tff(c_6359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6355, c_6277])).
% 5.89/2.18  tff(c_6361, plain, (![B_578]: (r2_hidden(B_578, '#skF_12') | ~r2_hidden(B_578, '#skF_10'))), inference(splitRight, [status(thm)], [c_5870])).
% 5.89/2.18  tff(c_6562, plain, (![B_584]: (r2_hidden('#skF_1'('#skF_10', B_584), '#skF_12') | r1_tarski('#skF_10', B_584))), inference(resolution, [status(thm)], [c_6, c_6361])).
% 5.89/2.18  tff(c_6568, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_6562, c_4])).
% 5.89/2.18  tff(c_6573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3036, c_3036, c_6568])).
% 5.89/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.18  
% 5.89/2.18  Inference rules
% 5.89/2.18  ----------------------
% 5.89/2.18  #Ref     : 0
% 5.89/2.18  #Sup     : 1493
% 5.89/2.18  #Fact    : 0
% 5.89/2.18  #Define  : 0
% 5.89/2.18  #Split   : 7
% 5.89/2.18  #Chain   : 0
% 5.89/2.18  #Close   : 0
% 5.89/2.18  
% 5.89/2.18  Ordering : KBO
% 5.89/2.18  
% 5.89/2.18  Simplification rules
% 5.89/2.18  ----------------------
% 5.89/2.18  #Subsume      : 525
% 5.89/2.18  #Demod        : 1011
% 5.89/2.18  #Tautology    : 492
% 5.89/2.18  #SimpNegUnit  : 30
% 5.89/2.18  #BackRed      : 92
% 5.89/2.18  
% 5.89/2.18  #Partial instantiations: 0
% 5.89/2.18  #Strategies tried      : 1
% 5.89/2.18  
% 5.89/2.18  Timing (in seconds)
% 5.89/2.18  ----------------------
% 5.89/2.18  Preprocessing        : 0.33
% 5.89/2.18  Parsing              : 0.18
% 5.89/2.18  CNF conversion       : 0.03
% 5.89/2.18  Main loop            : 1.06
% 5.89/2.18  Inferencing          : 0.43
% 5.89/2.18  Reduction            : 0.31
% 5.89/2.18  Demodulation         : 0.22
% 5.89/2.18  BG Simplification    : 0.04
% 5.89/2.18  Subsumption          : 0.20
% 5.89/2.18  Abstraction          : 0.05
% 5.89/2.18  MUC search           : 0.00
% 5.89/2.18  Cooper               : 0.00
% 5.89/2.18  Total                : 1.43
% 5.89/2.18  Index Insertion      : 0.00
% 5.89/2.18  Index Deletion       : 0.00
% 5.89/2.18  Index Matching       : 0.00
% 5.89/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
