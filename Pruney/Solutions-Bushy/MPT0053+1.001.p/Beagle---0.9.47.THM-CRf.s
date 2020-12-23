%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:38 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_10])).

tff(c_8,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8])).

%------------------------------------------------------------------------------
