%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:25 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 176 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 301 expanded)
%              Number of equality atoms :   11 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k5_xboole_0(B,C))
      <=> ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_24,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8512,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_94,plain,(
    ! [A_38,B_39] : k4_xboole_0(k2_xboole_0(A_38,B_39),k3_xboole_0(A_38,B_39)) = k5_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_45,A_46,B_47] :
      ( r1_tarski(A_45,k2_xboole_0(A_46,B_47))
      | ~ r1_tarski(A_45,k5_xboole_0(A_46,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_6])).

tff(c_166,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_159])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_166])).

tff(c_176,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    ! [A_56,A_57,B_58] :
      ( r1_xboole_0(A_56,k3_xboole_0(A_57,B_58))
      | ~ r1_tarski(A_56,k5_xboole_0(A_57,B_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4])).

tff(c_175,plain,
    ( ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_177,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_244,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_241,c_177])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_244])).

tff(c_253,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_329,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_253,c_24])).

tff(c_252,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_257,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_252,c_14])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,k2_xboole_0(B_10,C_11))
      | ~ r1_tarski(k4_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_265,plain,(
    ! [C_11] :
      ( r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),C_11))
      | ~ r1_tarski('#skF_1',C_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_10])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_437,plain,(
    ! [A_66,A_67,B_68] :
      ( r1_tarski(A_66,k2_xboole_0(A_67,B_68))
      | ~ r1_tarski(A_66,k5_xboole_0(A_67,B_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_6])).

tff(c_1300,plain,(
    ! [A_121,A_122,B_123] :
      ( r1_tarski(A_121,k2_xboole_0(A_122,k4_xboole_0(B_123,A_122)))
      | ~ r1_tarski(A_121,k2_xboole_0(A_122,B_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_437])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(k4_xboole_0(A_6,B_7),C_8)
      | ~ r1_tarski(A_6,k2_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_268,plain,(
    ! [C_8] :
      ( r1_tarski('#skF_1',C_8)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),C_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_8])).

tff(c_6022,plain,(
    ! [B_271] :
      ( r1_tarski('#skF_1',k4_xboole_0(B_271,k3_xboole_0('#skF_2','#skF_3')))
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),B_271)) ) ),
    inference(resolution,[status(thm)],[c_1300,c_268])).

tff(c_6058,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6022])).

tff(c_6067,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_6058])).

tff(c_6073,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_265,c_6067])).

tff(c_6080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_6073])).

tff(c_6082,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6083,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_6088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6082,c_6083])).

tff(c_6089,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_6081,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6094,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6081,c_14])).

tff(c_6177,plain,(
    ! [A_277,B_278,C_279] :
      ( r1_tarski(A_277,k2_xboole_0(B_278,C_279))
      | ~ r1_tarski(k4_xboole_0(A_277,B_278),C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6186,plain,(
    ! [C_279] :
      ( r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),C_279))
      | ~ r1_tarski('#skF_1',C_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6094,c_6177])).

tff(c_6191,plain,(
    ! [A_280,B_281] : k4_xboole_0(k2_xboole_0(A_280,B_281),k3_xboole_0(A_280,B_281)) = k5_xboole_0(A_280,B_281) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6301,plain,(
    ! [A_290,A_291,B_292] :
      ( r1_tarski(A_290,k2_xboole_0(A_291,B_292))
      | ~ r1_tarski(A_290,k5_xboole_0(A_291,B_292)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6191,c_6])).

tff(c_6662,plain,(
    ! [A_328,A_329,B_330] :
      ( r1_tarski(A_328,k2_xboole_0(A_329,k4_xboole_0(B_330,A_329)))
      | ~ r1_tarski(A_328,k2_xboole_0(A_329,B_330)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6301])).

tff(c_6152,plain,(
    ! [A_274,B_275,C_276] :
      ( r1_tarski(k4_xboole_0(A_274,B_275),C_276)
      | ~ r1_tarski(A_274,k2_xboole_0(B_275,C_276)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6170,plain,(
    ! [C_276] :
      ( r1_tarski('#skF_1',C_276)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),C_276)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6094,c_6152])).

tff(c_8396,plain,(
    ! [B_397] :
      ( r1_tarski('#skF_1',k4_xboole_0(B_397,k3_xboole_0('#skF_2','#skF_3')))
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),B_397)) ) ),
    inference(resolution,[status(thm)],[c_6662,c_6170])).

tff(c_8418,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8396])).

tff(c_8431,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_8418])).

tff(c_8446,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6186,c_8431])).

tff(c_8453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6089,c_8446])).

tff(c_8454,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_8460,plain,(
    ! [A_401,B_402] : k4_xboole_0(k2_xboole_0(A_401,B_402),k3_xboole_0(A_401,B_402)) = k5_xboole_0(A_401,B_402) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8555,plain,(
    ! [A_411,A_412,B_413] :
      ( r1_tarski(A_411,k2_xboole_0(A_412,B_413))
      | ~ r1_tarski(A_411,k5_xboole_0(A_412,B_413)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8460,c_6])).

tff(c_8565,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_8454,c_8555])).

tff(c_8574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8512,c_8565])).

tff(c_8576,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_8584,plain,(
    ! [A_414,A_415,B_416] :
      ( r1_xboole_0(A_414,k3_xboole_0(A_415,B_416))
      | ~ r1_tarski(A_414,k5_xboole_0(A_415,B_416)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8460,c_4])).

tff(c_8575,plain,
    ( ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_8577,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_8575])).

tff(c_8587,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_8584,c_8577])).

tff(c_8594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8454,c_8587])).

tff(c_8596,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_8575])).

tff(c_8455,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8576,c_8596,c_8455,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.76  
% 7.67/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.76  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.67/2.76  
% 7.67/2.76  %Foreground sorts:
% 7.67/2.76  
% 7.67/2.76  
% 7.67/2.76  %Background operators:
% 7.67/2.76  
% 7.67/2.76  
% 7.67/2.76  %Foreground operators:
% 7.67/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.67/2.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.67/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.67/2.76  tff('#skF_5', type, '#skF_5': $i).
% 7.67/2.76  tff('#skF_6', type, '#skF_6': $i).
% 7.67/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.67/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.67/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.67/2.76  tff('#skF_1', type, '#skF_1': $i).
% 7.67/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.67/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.67/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.67/2.76  
% 7.67/2.78  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 7.67/2.78  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 7.67/2.78  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.67/2.78  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.67/2.78  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.67/2.78  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.67/2.78  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.67/2.78  tff(c_24, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.78  tff(c_8512, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_24])).
% 7.67/2.78  tff(c_22, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.78  tff(c_130, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_22])).
% 7.67/2.78  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.78  tff(c_74, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_28])).
% 7.67/2.78  tff(c_94, plain, (![A_38, B_39]: (k4_xboole_0(k2_xboole_0(A_38, B_39), k3_xboole_0(A_38, B_39))=k5_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/2.78  tff(c_6, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.67/2.78  tff(c_159, plain, (![A_45, A_46, B_47]: (r1_tarski(A_45, k2_xboole_0(A_46, B_47)) | ~r1_tarski(A_45, k5_xboole_0(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_6])).
% 7.67/2.78  tff(c_166, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_159])).
% 7.67/2.78  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_166])).
% 7.67/2.78  tff(c_176, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_22])).
% 7.67/2.78  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.67/2.78  tff(c_241, plain, (![A_56, A_57, B_58]: (r1_xboole_0(A_56, k3_xboole_0(A_57, B_58)) | ~r1_tarski(A_56, k5_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4])).
% 7.67/2.78  tff(c_175, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_22])).
% 7.67/2.78  tff(c_177, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_175])).
% 7.67/2.78  tff(c_244, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_241, c_177])).
% 7.67/2.78  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_244])).
% 7.67/2.78  tff(c_253, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_175])).
% 7.67/2.78  tff(c_329, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_253, c_24])).
% 7.67/2.78  tff(c_252, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_175])).
% 7.67/2.78  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.67/2.78  tff(c_257, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_252, c_14])).
% 7.67/2.78  tff(c_10, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, k2_xboole_0(B_10, C_11)) | ~r1_tarski(k4_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.67/2.78  tff(c_265, plain, (![C_11]: (r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), C_11)) | ~r1_tarski('#skF_1', C_11))), inference(superposition, [status(thm), theory('equality')], [c_257, c_10])).
% 7.67/2.78  tff(c_26, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.78  tff(c_73, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 7.67/2.78  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/2.78  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.67/2.78  tff(c_437, plain, (![A_66, A_67, B_68]: (r1_tarski(A_66, k2_xboole_0(A_67, B_68)) | ~r1_tarski(A_66, k5_xboole_0(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_6])).
% 7.67/2.78  tff(c_1300, plain, (![A_121, A_122, B_123]: (r1_tarski(A_121, k2_xboole_0(A_122, k4_xboole_0(B_123, A_122))) | ~r1_tarski(A_121, k2_xboole_0(A_122, B_123)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_437])).
% 7.67/2.78  tff(c_8, plain, (![A_6, B_7, C_8]: (r1_tarski(k4_xboole_0(A_6, B_7), C_8) | ~r1_tarski(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.67/2.78  tff(c_268, plain, (![C_8]: (r1_tarski('#skF_1', C_8) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), C_8)))), inference(superposition, [status(thm), theory('equality')], [c_257, c_8])).
% 7.67/2.78  tff(c_6022, plain, (![B_271]: (r1_tarski('#skF_1', k4_xboole_0(B_271, k3_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), B_271)))), inference(resolution, [status(thm)], [c_1300, c_268])).
% 7.67/2.78  tff(c_6058, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k2_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6022])).
% 7.67/2.78  tff(c_6067, plain, (~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k2_xboole_0('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_73, c_6058])).
% 7.67/2.78  tff(c_6073, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_265, c_6067])).
% 7.67/2.78  tff(c_6080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_6073])).
% 7.67/2.78  tff(c_6082, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 7.67/2.78  tff(c_30, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.78  tff(c_6083, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_30])).
% 7.67/2.78  tff(c_6088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6082, c_6083])).
% 7.67/2.78  tff(c_6089, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 7.67/2.78  tff(c_6081, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 7.67/2.78  tff(c_6094, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_6081, c_14])).
% 7.67/2.78  tff(c_6177, plain, (![A_277, B_278, C_279]: (r1_tarski(A_277, k2_xboole_0(B_278, C_279)) | ~r1_tarski(k4_xboole_0(A_277, B_278), C_279))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.67/2.78  tff(c_6186, plain, (![C_279]: (r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), C_279)) | ~r1_tarski('#skF_1', C_279))), inference(superposition, [status(thm), theory('equality')], [c_6094, c_6177])).
% 7.67/2.78  tff(c_6191, plain, (![A_280, B_281]: (k4_xboole_0(k2_xboole_0(A_280, B_281), k3_xboole_0(A_280, B_281))=k5_xboole_0(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/2.78  tff(c_6301, plain, (![A_290, A_291, B_292]: (r1_tarski(A_290, k2_xboole_0(A_291, B_292)) | ~r1_tarski(A_290, k5_xboole_0(A_291, B_292)))), inference(superposition, [status(thm), theory('equality')], [c_6191, c_6])).
% 7.67/2.78  tff(c_6662, plain, (![A_328, A_329, B_330]: (r1_tarski(A_328, k2_xboole_0(A_329, k4_xboole_0(B_330, A_329))) | ~r1_tarski(A_328, k2_xboole_0(A_329, B_330)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6301])).
% 7.67/2.78  tff(c_6152, plain, (![A_274, B_275, C_276]: (r1_tarski(k4_xboole_0(A_274, B_275), C_276) | ~r1_tarski(A_274, k2_xboole_0(B_275, C_276)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.67/2.78  tff(c_6170, plain, (![C_276]: (r1_tarski('#skF_1', C_276) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), C_276)))), inference(superposition, [status(thm), theory('equality')], [c_6094, c_6152])).
% 7.67/2.78  tff(c_8396, plain, (![B_397]: (r1_tarski('#skF_1', k4_xboole_0(B_397, k3_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), B_397)))), inference(resolution, [status(thm)], [c_6662, c_6170])).
% 7.67/2.78  tff(c_8418, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k2_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8396])).
% 7.67/2.78  tff(c_8431, plain, (~r1_tarski('#skF_1', k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k2_xboole_0('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_73, c_8418])).
% 7.67/2.78  tff(c_8446, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6186, c_8431])).
% 7.67/2.78  tff(c_8453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6089, c_8446])).
% 7.67/2.78  tff(c_8454, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_26])).
% 7.67/2.78  tff(c_8460, plain, (![A_401, B_402]: (k4_xboole_0(k2_xboole_0(A_401, B_402), k3_xboole_0(A_401, B_402))=k5_xboole_0(A_401, B_402))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/2.78  tff(c_8555, plain, (![A_411, A_412, B_413]: (r1_tarski(A_411, k2_xboole_0(A_412, B_413)) | ~r1_tarski(A_411, k5_xboole_0(A_412, B_413)))), inference(superposition, [status(thm), theory('equality')], [c_8460, c_6])).
% 7.67/2.78  tff(c_8565, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_8454, c_8555])).
% 7.67/2.78  tff(c_8574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8512, c_8565])).
% 7.67/2.78  tff(c_8576, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_24])).
% 7.67/2.78  tff(c_8584, plain, (![A_414, A_415, B_416]: (r1_xboole_0(A_414, k3_xboole_0(A_415, B_416)) | ~r1_tarski(A_414, k5_xboole_0(A_415, B_416)))), inference(superposition, [status(thm), theory('equality')], [c_8460, c_4])).
% 7.67/2.78  tff(c_8575, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 7.67/2.78  tff(c_8577, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_8575])).
% 7.67/2.78  tff(c_8587, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_8584, c_8577])).
% 7.67/2.78  tff(c_8594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8454, c_8587])).
% 7.67/2.78  tff(c_8596, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_8575])).
% 7.67/2.78  tff(c_8455, plain, (r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 7.67/2.78  tff(c_20, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/2.78  tff(c_8629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8576, c_8596, c_8455, c_20])).
% 7.67/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.78  
% 7.67/2.78  Inference rules
% 7.67/2.78  ----------------------
% 7.67/2.78  #Ref     : 0
% 7.67/2.78  #Sup     : 2359
% 7.67/2.78  #Fact    : 0
% 7.67/2.78  #Define  : 0
% 7.67/2.78  #Split   : 32
% 7.67/2.78  #Chain   : 0
% 7.67/2.78  #Close   : 0
% 7.67/2.78  
% 7.67/2.78  Ordering : KBO
% 7.67/2.78  
% 7.67/2.78  Simplification rules
% 7.67/2.78  ----------------------
% 7.67/2.78  #Subsume      : 445
% 7.67/2.78  #Demod        : 392
% 7.67/2.78  #Tautology    : 326
% 7.67/2.78  #SimpNegUnit  : 6
% 7.67/2.78  #BackRed      : 0
% 7.67/2.78  
% 7.67/2.78  #Partial instantiations: 0
% 7.67/2.78  #Strategies tried      : 1
% 7.67/2.78  
% 7.67/2.78  Timing (in seconds)
% 7.67/2.78  ----------------------
% 7.67/2.78  Preprocessing        : 0.27
% 7.67/2.78  Parsing              : 0.15
% 7.67/2.78  CNF conversion       : 0.02
% 7.67/2.78  Main loop            : 1.73
% 7.67/2.78  Inferencing          : 0.53
% 7.67/2.78  Reduction            : 0.56
% 7.67/2.78  Demodulation         : 0.37
% 7.67/2.78  BG Simplification    : 0.07
% 7.67/2.78  Subsumption          : 0.45
% 7.67/2.78  Abstraction          : 0.06
% 7.67/2.78  MUC search           : 0.00
% 7.67/2.78  Cooper               : 0.00
% 7.67/2.78  Total                : 2.03
% 7.67/2.78  Index Insertion      : 0.00
% 7.67/2.78  Index Deletion       : 0.00
% 7.67/2.78  Index Matching       : 0.00
% 7.67/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
