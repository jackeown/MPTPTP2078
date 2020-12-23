%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0112+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:44 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_8,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15,plain,(
    ! [B_5,A_6] :
      ( ~ r2_xboole_0(B_5,A_6)
      | ~ r1_tarski(A_6,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_27,plain,(
    k4_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_19])).

tff(c_32,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_27])).

%------------------------------------------------------------------------------
