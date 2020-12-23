%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0904+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:03 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   50 (  94 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 170 expanded)
%              Number of equality atoms :    3 (  16 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ~ r1_xboole_0(k4_zfmisc_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
       => ( ~ r1_xboole_0(A,E)
          & ~ r1_xboole_0(B,F)
          & ~ r1_xboole_0(C,G)
          & ~ r1_xboole_0(D,H) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

tff(c_8,plain,
    ( r1_xboole_0('#skF_4','#skF_8')
    | r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_2','#skF_6')
    | r1_xboole_0('#skF_1','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    r1_xboole_0('#skF_1','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7),D_8) = k4_zfmisc_1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19),D_20) = k4_zfmisc_1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [D_55,A_53,D_56,B_57,C_52,B_54] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_53,B_54),C_52),B_57)
      | r1_xboole_0(k4_zfmisc_1(A_53,B_54,C_52,D_55),k2_zfmisc_1(B_57,D_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_4])).

tff(c_189,plain,(
    ! [D_81,D_80,C_84,B_82,B_85,D_83,A_79] :
      ( r1_xboole_0(k4_zfmisc_1(A_79,B_85,C_84,D_83),k2_zfmisc_1(k2_zfmisc_1(B_82,D_80),D_81))
      | ~ r1_xboole_0(k2_zfmisc_1(A_79,B_85),B_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_261,plain,(
    ! [B_126,D_127,C_128,D_122,B_125,A_123,A_129,C_124] :
      ( r1_xboole_0(k4_zfmisc_1(A_123,B_126,C_124,D_127),k4_zfmisc_1(A_129,B_125,C_128,D_122))
      | ~ r1_xboole_0(k2_zfmisc_1(A_123,B_126),k2_zfmisc_1(A_129,B_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_189])).

tff(c_10,plain,(
    ~ r1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_277,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_261,c_10])).

tff(c_285,plain,(
    ~ r1_xboole_0('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_277])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_285])).

tff(c_291,plain,
    ( r1_xboole_0('#skF_2','#skF_6')
    | r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_293,plain,(
    r1_xboole_0('#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_2,plain,(
    ! [C_3,D_4,A_1,B_2] :
      ( ~ r1_xboole_0(C_3,D_4)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_294,plain,(
    ! [D_133,B_132,C_130,A_131,C_134,A_135] :
      ( ~ r1_xboole_0(C_134,D_133)
      | r1_xboole_0(k2_zfmisc_1(A_135,C_134),k4_zfmisc_1(A_131,B_132,C_130,D_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_2])).

tff(c_322,plain,(
    ! [C_152,A_154,D_147,D_153,B_149,A_148,B_151,C_150] :
      ( ~ r1_xboole_0(D_147,D_153)
      | r1_xboole_0(k4_zfmisc_1(A_154,B_151,C_152,D_147),k4_zfmisc_1(A_148,B_149,C_150,D_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_294])).

tff(c_325,plain,(
    ~ r1_xboole_0('#skF_4','#skF_8') ),
    inference(resolution,[status(thm)],[c_322,c_10])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_325])).

tff(c_336,plain,
    ( r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_338,plain,(
    r1_xboole_0('#skF_2','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_386,plain,(
    ! [B_188,B_191,A_187,D_189,D_190,C_186] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_187,B_188),C_186),B_191)
      | r1_xboole_0(k4_zfmisc_1(A_187,B_188,C_186,D_189),k2_zfmisc_1(B_191,D_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_4])).

tff(c_437,plain,(
    ! [C_222,D_220,A_218,B_221,D_216,D_219,B_217] :
      ( r1_xboole_0(k4_zfmisc_1(A_218,B_217,C_222,D_216),k2_zfmisc_1(k2_zfmisc_1(B_221,D_219),D_220))
      | ~ r1_xboole_0(k2_zfmisc_1(A_218,B_217),B_221) ) ),
    inference(resolution,[status(thm)],[c_4,c_386])).

tff(c_570,plain,(
    ! [B_267,D_265,C_271,A_272,D_266,C_269,B_268,A_270] :
      ( r1_xboole_0(k4_zfmisc_1(A_272,B_267,C_271,D_266),k4_zfmisc_1(A_270,B_268,C_269,D_265))
      | ~ r1_xboole_0(k2_zfmisc_1(A_272,B_267),k2_zfmisc_1(A_270,B_268)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_437])).

tff(c_586,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_570,c_10])).

tff(c_591,plain,(
    ~ r1_xboole_0('#skF_2','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_586])).

tff(c_598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_591])).

tff(c_599,plain,(
    r1_xboole_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_640,plain,(
    ! [D_301,A_299,B_300,D_302,B_303,C_298] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_299,B_300),C_298),B_303)
      | r1_xboole_0(k4_zfmisc_1(A_299,B_300,C_298,D_301),k2_zfmisc_1(B_303,D_302)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_4])).

tff(c_659,plain,(
    ! [D_307,A_304,D_308,B_306,D_305,C_310,B_309] :
      ( r1_xboole_0(k4_zfmisc_1(A_304,B_306,C_310,D_305),k2_zfmisc_1(k2_zfmisc_1(B_309,D_308),D_307))
      | ~ r1_xboole_0(C_310,D_308) ) ),
    inference(resolution,[status(thm)],[c_2,c_640])).

tff(c_681,plain,(
    ! [D_324,D_317,C_318,C_321,A_322,B_320,B_319,A_323] :
      ( r1_xboole_0(k4_zfmisc_1(A_323,B_319,C_318,D_324),k4_zfmisc_1(A_322,B_320,C_321,D_317))
      | ~ r1_xboole_0(C_318,C_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_659])).

tff(c_684,plain,(
    ~ r1_xboole_0('#skF_3','#skF_7') ),
    inference(resolution,[status(thm)],[c_681,c_10])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_684])).

%------------------------------------------------------------------------------
