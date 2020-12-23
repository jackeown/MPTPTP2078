%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:44 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 250 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 556 expanded)
%              Number of equality atoms :   28 ( 123 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,axiom,(
    ! [A,B] : r3_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r2_xboole_0(A,B)
            & A != B
            & ~ r2_xboole_0(B,A) )
      <=> r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(c_14,plain,(
    ! [A_5] : r3_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [B_17,A_18] :
      ( r1_tarski(B_17,A_18)
      | r1_tarski(A_18,B_17)
      | ~ r3_xboole_0(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_34,plain,(
    ! [A_9,B_10] :
      ( ~ r1_tarski(A_9,B_10)
      | r3_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_33,plain,(
    ~ r3_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_33])).

tff(c_39,plain,(
    ! [B_11,A_12] :
      ( ~ r1_tarski(B_11,A_12)
      | r3_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_39,c_33])).

tff(c_30,plain,
    ( r3_xboole_0('#skF_1','#skF_2')
    | r2_xboole_0('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_6])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_74])).

tff(c_80,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,
    ( '#skF_2' != '#skF_1'
    | r2_xboole_0('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,
    ( ~ r2_xboole_0('#skF_1','#skF_2')
    | r2_xboole_0('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,
    ( ~ r2_xboole_0('#skF_1','#skF_2')
    | r2_xboole_0('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_28])).

tff(c_100,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_103,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_103])).

tff(c_24,plain,
    ( ~ r2_xboole_0('#skF_2','#skF_1')
    | r2_xboole_0('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_88,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_88])).

tff(c_79,plain,
    ( '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_4','#skF_3')
    | r3_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_92,plain,(
    r3_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(B_4,A_3)
      | r1_tarski(A_3,B_4)
      | ~ r3_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,
    ( r1_tarski('#skF_2','#skF_1')
    | r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_98,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_95])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_98])).

tff(c_108,plain,
    ( '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_115,plain,(
    r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_118,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_118])).

tff(c_123,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_126,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_43])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_126])).

tff(c_132,plain,
    ( r2_xboole_0('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_144,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_43])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_144])).

tff(c_150,plain,(
    r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_161,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_6])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_161])).

tff(c_166,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_190,plain,
    ( '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_166])).

tff(c_191,plain,(
    r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_194,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_6])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_194])).

tff(c_199,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_202,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_43])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_202])).

tff(c_208,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_214,plain,(
    r2_xboole_0('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_217,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_214,c_6])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_217])).

tff(c_222,plain,
    ( '#skF_3' = '#skF_4'
    | r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_230,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_233,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_230,c_6])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_233])).

tff(c_238,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_241,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_43])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_241])).

tff(c_247,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_258,plain,(
    ! [A_26,B_27] :
      ( r2_xboole_0(A_26,B_27)
      | B_27 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_248,plain,(
    r3_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( ~ r2_xboole_0('#skF_1','#skF_2')
    | ~ r3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_252,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_20])).

tff(c_264,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_258,c_252])).

tff(c_275,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_264])).

tff(c_16,plain,
    ( ~ r2_xboole_0('#skF_2','#skF_1')
    | ~ r3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_250,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_16])).

tff(c_267,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_258,c_250])).

tff(c_278,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_267])).

tff(c_22,plain,
    ( r3_xboole_0('#skF_1','#skF_2')
    | ~ r3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_256,plain,(
    r3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_22])).

tff(c_281,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(B_28,A_29)
      | r1_tarski(A_29,B_28)
      | ~ r3_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,
    ( r1_tarski('#skF_2','#skF_1')
    | r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_256,c_281])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_278,c_287])).

%------------------------------------------------------------------------------
