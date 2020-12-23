%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0120+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:45 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   13 (  15 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   7 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') != k2_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_4])).

%------------------------------------------------------------------------------
