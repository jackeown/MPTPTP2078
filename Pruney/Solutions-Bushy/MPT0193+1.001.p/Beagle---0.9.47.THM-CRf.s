%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0193+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:53 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   23 (  49 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  41 expanded)
%              Number of equality atoms :   14 (  40 expanded)
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

tff(f_26,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_28,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_31,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_42,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,B_13,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_172,plain,(
    ! [C_21,A_22,D_23,B_24] : k2_enumset1(C_21,A_22,D_23,B_24) = k2_enumset1(A_22,B_24,C_21,D_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_256,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_57,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,D_16,C_14,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_244,plain,(
    ! [A_15,D_16,C_14,B_13] : k2_enumset1(A_15,D_16,C_14,B_13) = k2_enumset1(A_15,B_13,D_16,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_172])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_7])).

tff(c_547,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8])).

tff(c_1397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_244,c_547])).

%------------------------------------------------------------------------------
