%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0290+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:03 EST 2020

% Result     : Theorem 11.76s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 143 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 358 expanded)
%              Number of equality atoms :   13 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > #skF_6 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_51,C_52] :
      ( r2_hidden('#skF_5'(A_51,k3_tarski(A_51),C_52),A_51)
      | ~ r2_hidden(C_52,k3_tarski(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [D_30,A_25,B_26] :
      ( r2_hidden(D_30,A_25)
      | ~ r2_hidden(D_30,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_109,plain,(
    ! [A_25,B_26,C_52] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_25,B_26),k3_tarski(k3_xboole_0(A_25,B_26)),C_52),A_25)
      | ~ r2_hidden(C_52,k3_tarski(k3_xboole_0(A_25,B_26))) ) ),
    inference(resolution,[status(thm)],[c_93,c_30])).

tff(c_58,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_748,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden('#skF_6'(A_138,B_139,C_140),B_139)
      | r2_hidden('#skF_7'(A_138,B_139,C_140),C_140)
      | k3_xboole_0(A_138,B_139) = C_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r2_hidden('#skF_6'(A_25,B_26,C_27),C_27)
      | r2_hidden('#skF_7'(A_25,B_26,C_27),C_27)
      | k3_xboole_0(A_25,B_26) = C_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_818,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_7'(A_141,B_142,B_142),B_142)
      | k3_xboole_0(A_141,B_142) = B_142 ) ),
    inference(resolution,[status(thm)],[c_748,c_38])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_848,plain,(
    ! [A_141,B_142,B_2] :
      ( r2_hidden('#skF_7'(A_141,B_142,B_142),B_2)
      | ~ r1_tarski(B_142,B_2)
      | k3_xboole_0(A_141,B_142) = B_142 ) ),
    inference(resolution,[status(thm)],[c_818,c_2])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden('#skF_6'(A_25,B_26,C_27),A_25)
      | r2_hidden('#skF_7'(A_25,B_26,C_27),C_27)
      | k3_xboole_0(A_25,B_26) = C_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1466,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden('#skF_6'(A_191,B_192,C_193),A_191)
      | ~ r2_hidden('#skF_7'(A_191,B_192,C_193),B_192)
      | ~ r2_hidden('#skF_7'(A_191,B_192,C_193),A_191)
      | k3_xboole_0(A_191,B_192) = C_193 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1495,plain,(
    ! [A_25,C_27] :
      ( ~ r2_hidden('#skF_7'(A_25,C_27,C_27),A_25)
      | r2_hidden('#skF_6'(A_25,C_27,C_27),A_25)
      | k3_xboole_0(A_25,C_27) = C_27 ) ),
    inference(resolution,[status(thm)],[c_42,c_1466])).

tff(c_1704,plain,(
    ! [A_203,B_204,C_205] :
      ( ~ r2_hidden('#skF_6'(A_203,B_204,C_205),C_205)
      | ~ r2_hidden('#skF_7'(A_203,B_204,C_205),B_204)
      | ~ r2_hidden('#skF_7'(A_203,B_204,C_205),A_203)
      | k3_xboole_0(A_203,B_204) = C_205 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1756,plain,(
    ! [A_209] :
      ( ~ r2_hidden('#skF_7'(A_209,A_209,A_209),A_209)
      | k3_xboole_0(A_209,A_209) = A_209 ) ),
    inference(resolution,[status(thm)],[c_1495,c_1704])).

tff(c_1760,plain,(
    ! [B_2] :
      ( ~ r1_tarski(B_2,B_2)
      | k3_xboole_0(B_2,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_848,c_1756])).

tff(c_1787,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1760])).

tff(c_73,plain,(
    ! [D_48,A_49,B_50] :
      ( r2_hidden(D_48,k3_xboole_0(A_49,B_50))
      | ~ r2_hidden(D_48,B_50)
      | ~ r2_hidden(D_48,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k3_tarski(A_6))
      | ~ r2_hidden(D_24,A_6)
      | ~ r2_hidden(C_21,D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_515,plain,(
    ! [C_116,A_117,B_118,D_119] :
      ( r2_hidden(C_116,k3_tarski(k3_xboole_0(A_117,B_118)))
      | ~ r2_hidden(C_116,D_119)
      | ~ r2_hidden(D_119,B_118)
      | ~ r2_hidden(D_119,A_117) ) ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_3764,plain,(
    ! [A_330,B_331,A_332,B_333] :
      ( r2_hidden('#skF_1'(A_330,B_331),k3_tarski(k3_xboole_0(A_332,B_333)))
      | ~ r2_hidden(A_330,B_333)
      | ~ r2_hidden(A_330,A_332)
      | r1_tarski(A_330,B_331) ) ),
    inference(resolution,[status(thm)],[c_6,c_515])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3785,plain,(
    ! [A_334,B_335,A_336] :
      ( ~ r2_hidden(A_334,B_335)
      | ~ r2_hidden(A_334,A_336)
      | r1_tarski(A_334,k3_tarski(k3_xboole_0(A_336,B_335))) ) ),
    inference(resolution,[status(thm)],[c_3764,c_4])).

tff(c_3810,plain,(
    ! [A_337,B_338] :
      ( ~ r2_hidden(A_337,B_338)
      | ~ r2_hidden(A_337,B_338)
      | r1_tarski(A_337,k3_tarski(B_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_3785])).

tff(c_110,plain,(
    ! [C_53,A_54] :
      ( r2_hidden(C_53,'#skF_5'(A_54,k3_tarski(A_54),C_53))
      | ~ r2_hidden(C_53,k3_tarski(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [C_53,B_2,A_54] :
      ( r2_hidden(C_53,B_2)
      | ~ r1_tarski('#skF_5'(A_54,k3_tarski(A_54),C_53),B_2)
      | ~ r2_hidden(C_53,k3_tarski(A_54)) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_4161,plain,(
    ! [C_360,B_361,A_362] :
      ( r2_hidden(C_360,k3_tarski(B_361))
      | ~ r2_hidden(C_360,k3_tarski(A_362))
      | ~ r2_hidden('#skF_5'(A_362,k3_tarski(A_362),C_360),B_361) ) ),
    inference(resolution,[status(thm)],[c_3810,c_116])).

tff(c_4193,plain,(
    ! [C_363,A_364,B_365] :
      ( r2_hidden(C_363,k3_tarski(A_364))
      | ~ r2_hidden(C_363,k3_tarski(k3_xboole_0(A_364,B_365))) ) ),
    inference(resolution,[status(thm)],[c_109,c_4161])).

tff(c_7301,plain,(
    ! [A_423,B_424,B_425] :
      ( r2_hidden('#skF_1'(k3_tarski(k3_xboole_0(A_423,B_424)),B_425),k3_tarski(A_423))
      | r1_tarski(k3_tarski(k3_xboole_0(A_423,B_424)),B_425) ) ),
    inference(resolution,[status(thm)],[c_6,c_4193])).

tff(c_7369,plain,(
    ! [A_423,B_424] : r1_tarski(k3_tarski(k3_xboole_0(A_423,B_424)),k3_tarski(A_423)) ),
    inference(resolution,[status(thm)],[c_7301,c_4])).

tff(c_28,plain,(
    ! [D_30,B_26,A_25] :
      ( r2_hidden(D_30,B_26)
      | ~ r2_hidden(D_30,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    ! [A_25,B_26,C_52] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_25,B_26),k3_tarski(k3_xboole_0(A_25,B_26)),C_52),B_26)
      | ~ r2_hidden(C_52,k3_tarski(k3_xboole_0(A_25,B_26))) ) ),
    inference(resolution,[status(thm)],[c_93,c_28])).

tff(c_4406,plain,(
    ! [C_366,B_367,A_368] :
      ( r2_hidden(C_366,k3_tarski(B_367))
      | ~ r2_hidden(C_366,k3_tarski(k3_xboole_0(A_368,B_367))) ) ),
    inference(resolution,[status(thm)],[c_108,c_4161])).

tff(c_7397,plain,(
    ! [A_428,B_429,B_430] :
      ( r2_hidden('#skF_1'(k3_tarski(k3_xboole_0(A_428,B_429)),B_430),k3_tarski(B_429))
      | r1_tarski(k3_tarski(k3_xboole_0(A_428,B_429)),B_430) ) ),
    inference(resolution,[status(thm)],[c_6,c_4406])).

tff(c_7465,plain,(
    ! [A_428,B_429] : r1_tarski(k3_tarski(k3_xboole_0(A_428,B_429)),k3_tarski(B_429)) ),
    inference(resolution,[status(thm)],[c_7397,c_4])).

tff(c_65,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_1,B_2,B_43] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_43)
      | ~ r1_tarski(A_1,B_43)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_13250,plain,(
    ! [A_563,A_564,B_565] :
      ( r1_tarski(A_563,k3_xboole_0(A_564,B_565))
      | ~ r2_hidden('#skF_1'(A_563,k3_xboole_0(A_564,B_565)),B_565)
      | ~ r2_hidden('#skF_1'(A_563,k3_xboole_0(A_564,B_565)),A_564) ) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_18204,plain,(
    ! [A_672,A_673,B_674] :
      ( ~ r2_hidden('#skF_1'(A_672,k3_xboole_0(A_673,B_674)),A_673)
      | ~ r1_tarski(A_672,B_674)
      | r1_tarski(A_672,k3_xboole_0(A_673,B_674)) ) ),
    inference(resolution,[status(thm)],[c_68,c_13250])).

tff(c_18443,plain,(
    ! [A_677,B_678,B_679] :
      ( ~ r1_tarski(A_677,B_678)
      | ~ r1_tarski(A_677,B_679)
      | r1_tarski(A_677,k3_xboole_0(B_679,B_678)) ) ),
    inference(resolution,[status(thm)],[c_68,c_18204])).

tff(c_44,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_8','#skF_9')),k3_xboole_0(k3_tarski('#skF_8'),k3_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18514,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_8','#skF_9')),k3_tarski('#skF_9'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_8','#skF_9')),k3_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18443,c_44])).

tff(c_18550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7369,c_7465,c_18514])).

%------------------------------------------------------------------------------
