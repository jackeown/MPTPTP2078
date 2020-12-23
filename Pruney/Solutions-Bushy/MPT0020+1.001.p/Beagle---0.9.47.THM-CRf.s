%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0020+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:35 EST 2020

% Result     : Theorem 19.65s
% Output     : CNFRefutation 19.75s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 280 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  125 ( 789 expanded)
%              Number of equality atoms :   23 ( 164 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_6'),k2_xboole_0('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [A_62,A_63,B_64] :
      ( r1_tarski(A_62,k2_xboole_0(A_63,B_64))
      | ~ r2_hidden('#skF_1'(A_62,k2_xboole_0(A_63,B_64)),B_64) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_244,plain,(
    ! [A_1,A_63] : r1_tarski(A_1,k2_xboole_0(A_63,A_1)) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1093,plain,(
    ! [B_160,C_161] :
      ( r2_hidden('#skF_3'(B_160,B_160,C_161),C_161)
      | k2_xboole_0(B_160,B_160) = C_161
      | r2_hidden('#skF_2'(B_160,B_160,C_161),B_160) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_24])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1144,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_3'(B_160,B_160,B_160),B_160)
      | k2_xboole_0(B_160,B_160) = B_160 ) ),
    inference(resolution,[status(thm)],[c_1093,c_22])).

tff(c_16,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2226,plain,(
    ! [A_227,C_228] :
      ( ~ r2_hidden('#skF_3'(A_227,A_227,C_228),A_227)
      | k2_xboole_0(A_227,A_227) = C_228
      | r2_hidden('#skF_2'(A_227,A_227,C_228),A_227) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_16])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2272,plain,(
    ! [A_229] :
      ( ~ r2_hidden('#skF_3'(A_229,A_229,A_229),A_229)
      | k2_xboole_0(A_229,A_229) = A_229 ) ),
    inference(resolution,[status(thm)],[c_2226,c_14])).

tff(c_2347,plain,(
    ! [B_160] : k2_xboole_0(B_160,B_160) = B_160 ),
    inference(resolution,[status(thm)],[c_1144,c_2272])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_1,B_2,B_24] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_24)
      | ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [A_40,A_41,B_42] :
      ( r1_tarski(A_40,k2_xboole_0(A_41,B_42))
      | ~ r2_hidden('#skF_1'(A_40,k2_xboole_0(A_41,B_42)),A_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

tff(c_116,plain,(
    ! [A_1,B_24,B_42] :
      ( ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,k2_xboole_0(B_24,B_42)) ) ),
    inference(resolution,[status(thm)],[c_58,c_99])).

tff(c_820,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_2'(A_132,B_133,C_134),B_133)
      | r2_hidden('#skF_2'(A_132,B_133,C_134),A_132)
      | r2_hidden('#skF_3'(A_132,B_133,C_134),C_134)
      | k2_xboole_0(A_132,B_133) = C_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_889,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_2'(A_132,B_133,B_133),A_132)
      | r2_hidden('#skF_3'(A_132,B_133,B_133),B_133)
      | k2_xboole_0(A_132,B_133) = B_133 ) ),
    inference(resolution,[status(thm)],[c_820,c_22])).

tff(c_622,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden('#skF_2'(A_114,B_115,C_116),B_115)
      | r2_hidden('#skF_2'(A_114,B_115,C_116),A_114)
      | ~ r2_hidden('#skF_3'(A_114,B_115,C_116),B_115)
      | k2_xboole_0(A_114,B_115) = C_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2732,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_2'(A_239,B_240,B_240),A_239)
      | ~ r2_hidden('#skF_3'(A_239,B_240,B_240),B_240)
      | k2_xboole_0(A_239,B_240) = B_240 ) ),
    inference(resolution,[status(thm)],[c_622,c_14])).

tff(c_2793,plain,(
    ! [A_241,B_242] :
      ( r2_hidden('#skF_2'(A_241,B_242,B_242),A_241)
      | k2_xboole_0(A_241,B_242) = B_242 ) ),
    inference(resolution,[status(thm)],[c_889,c_2732])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3189,plain,(
    ! [A_267,B_268,B_269] :
      ( r2_hidden('#skF_2'(A_267,B_268,B_268),B_269)
      | ~ r1_tarski(A_267,B_269)
      | k2_xboole_0(A_267,B_268) = B_268 ) ),
    inference(resolution,[status(thm)],[c_2793,c_2])).

tff(c_3387,plain,(
    ! [A_275,B_276] :
      ( r2_hidden('#skF_3'(A_275,B_276,B_276),B_276)
      | ~ r1_tarski(A_275,B_276)
      | k2_xboole_0(A_275,B_276) = B_276 ) ),
    inference(resolution,[status(thm)],[c_3189,c_22])).

tff(c_3230,plain,(
    ! [A_267,B_269] :
      ( ~ r2_hidden('#skF_3'(A_267,B_269,B_269),B_269)
      | ~ r1_tarski(A_267,B_269)
      | k2_xboole_0(A_267,B_269) = B_269 ) ),
    inference(resolution,[status(thm)],[c_3189,c_14])).

tff(c_3437,plain,(
    ! [A_277,B_278] :
      ( ~ r1_tarski(A_277,B_278)
      | k2_xboole_0(A_277,B_278) = B_278 ) ),
    inference(resolution,[status(thm)],[c_3387,c_3230])).

tff(c_7857,plain,(
    ! [A_352,B_353,B_354] :
      ( k2_xboole_0(A_352,k2_xboole_0(B_353,B_354)) = k2_xboole_0(B_353,B_354)
      | ~ r1_tarski(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_116,c_3437])).

tff(c_8549,plain,(
    ! [A_364,A_365,B_366,B_367] :
      ( ~ r1_tarski(A_364,A_365)
      | r1_tarski(A_364,k2_xboole_0(B_366,B_367))
      | ~ r1_tarski(A_365,B_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7857,c_116])).

tff(c_8613,plain,(
    ! [B_368,B_369] :
      ( r1_tarski('#skF_6',k2_xboole_0(B_368,B_369))
      | ~ r1_tarski('#skF_7',B_368) ) ),
    inference(resolution,[status(thm)],[c_28,c_8549])).

tff(c_8658,plain,(
    ! [B_370] :
      ( r1_tarski('#skF_6',B_370)
      | ~ r1_tarski('#skF_7',B_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2347,c_8613])).

tff(c_8756,plain,(
    ! [A_371] : r1_tarski('#skF_6',k2_xboole_0(A_371,'#skF_7')) ),
    inference(resolution,[status(thm)],[c_244,c_8658])).

tff(c_3423,plain,(
    ! [A_275,B_276] :
      ( ~ r1_tarski(A_275,B_276)
      | k2_xboole_0(A_275,B_276) = B_276 ) ),
    inference(resolution,[status(thm)],[c_3387,c_3230])).

tff(c_8771,plain,(
    ! [A_371] : k2_xboole_0('#skF_6',k2_xboole_0(A_371,'#skF_7')) = k2_xboole_0(A_371,'#skF_7') ),
    inference(resolution,[status(thm)],[c_8756,c_3423])).

tff(c_117,plain,(
    ! [A_1,B_42] : r1_tarski(A_1,k2_xboole_0(A_1,B_42)) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8968,plain,(
    ! [B_377,B_378] :
      ( r1_tarski('#skF_4',k2_xboole_0(B_377,B_378))
      | ~ r1_tarski('#skF_5',B_377) ) ),
    inference(resolution,[status(thm)],[c_30,c_8549])).

tff(c_9013,plain,(
    ! [B_379] :
      ( r1_tarski('#skF_4',B_379)
      | ~ r1_tarski('#skF_5',B_379) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2347,c_8968])).

tff(c_9180,plain,(
    ! [B_383] : r1_tarski('#skF_4',k2_xboole_0('#skF_5',B_383)) ),
    inference(resolution,[status(thm)],[c_117,c_9013])).

tff(c_9225,plain,(
    ! [B_383] : k2_xboole_0('#skF_4',k2_xboole_0('#skF_5',B_383)) = k2_xboole_0('#skF_5',B_383) ),
    inference(resolution,[status(thm)],[c_9180,c_3423])).

tff(c_61,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | r2_hidden(D_26,A_28)
      | ~ r2_hidden(D_26,k2_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7304,plain,(
    ! [A_347,B_348,B_349] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_347,B_348),B_349),B_348)
      | r2_hidden('#skF_1'(k2_xboole_0(A_347,B_348),B_349),A_347)
      | r1_tarski(k2_xboole_0(A_347,B_348),B_349) ) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_49,plain,(
    ! [A_20,A_6,B_7] :
      ( r1_tarski(A_20,k2_xboole_0(A_6,B_7))
      | ~ r2_hidden('#skF_1'(A_20,k2_xboole_0(A_6,B_7)),A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

tff(c_43486,plain,(
    ! [A_925,B_926,B_927] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_925,B_926),k2_xboole_0(B_926,B_927)),A_925)
      | r1_tarski(k2_xboole_0(A_925,B_926),k2_xboole_0(B_926,B_927)) ) ),
    inference(resolution,[status(thm)],[c_7304,c_49])).

tff(c_246,plain,(
    ! [A_62,A_63,A_6,B_7] :
      ( r1_tarski(A_62,k2_xboole_0(A_63,k2_xboole_0(A_6,B_7)))
      | ~ r2_hidden('#skF_1'(A_62,k2_xboole_0(A_63,k2_xboole_0(A_6,B_7))),A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_43732,plain,(
    ! [A_928,B_929,B_930] : r1_tarski(k2_xboole_0(A_928,B_929),k2_xboole_0(B_929,k2_xboole_0(A_928,B_930))) ),
    inference(resolution,[status(thm)],[c_43486,c_246])).

tff(c_50838,plain,(
    ! [B_976,B_977] : r1_tarski(k2_xboole_0('#skF_4',B_976),k2_xboole_0(B_976,k2_xboole_0('#skF_5',B_977))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9225,c_43732])).

tff(c_50935,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_6'),k2_xboole_0('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8771,c_50838])).

tff(c_51088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_50935])).

%------------------------------------------------------------------------------
