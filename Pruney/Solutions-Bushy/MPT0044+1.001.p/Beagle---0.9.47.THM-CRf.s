%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:37 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  58 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_33,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k1_xboole_0
      <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_12,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_20,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_26,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_13])).

tff(c_31,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_33,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_39,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_47,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_10,plain,
    ( k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0
    | k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_53])).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_6,plain,
    ( k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_55,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_59,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_59])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_71])).

%------------------------------------------------------------------------------
