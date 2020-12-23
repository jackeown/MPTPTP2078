%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0198+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:53 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   20 (  35 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  27 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_28,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_26,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_31,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_37,plain,(
    ! [C_13,B_14,A_15,D_16] : k2_enumset1(C_13,B_14,A_15,D_16) = k2_enumset1(A_15,B_14,C_13,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [C_7,B_6,A_5,D_8] : k2_enumset1(C_7,B_6,A_5,D_8) = k2_enumset1(A_5,C_7,D_8,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_85,plain,(
    ! [D_8,C_7,A_5,B_6] : k2_enumset1(D_8,C_7,A_5,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_94,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_7])).

tff(c_95,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79,c_95])).

%------------------------------------------------------------------------------
