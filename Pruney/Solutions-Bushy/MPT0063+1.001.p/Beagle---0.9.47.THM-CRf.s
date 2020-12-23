%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0063+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:39 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

tff(c_14,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_12,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    ! [A_11,C_12,B_13] :
      ( r2_xboole_0(A_11,C_12)
      | ~ r2_xboole_0(B_13,C_12)
      | ~ r1_tarski(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_14] :
      ( r2_xboole_0(A_14,'#skF_3')
      | ~ r1_tarski(A_14,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_10,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_10])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_59])).

%------------------------------------------------------------------------------
