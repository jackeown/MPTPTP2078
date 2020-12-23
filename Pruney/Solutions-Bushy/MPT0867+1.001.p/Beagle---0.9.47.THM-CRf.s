%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0867+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:59 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

tff(c_80,plain,(
    ! [A_23,B_24,C_25] : k2_zfmisc_1(k1_tarski(A_23),k2_tarski(B_24,C_25)) = k2_tarski(k4_tarski(A_23,B_24),k4_tarski(A_23,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k2_tarski(A_9,B_10),k2_tarski(C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,(
    ! [C_11,A_23,B_24,C_25,D_12] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_23),k2_tarski(B_24,C_25)),k2_tarski(C_11,D_12)) = k2_enumset1(k4_tarski(A_23,B_24),k4_tarski(A_23,C_25),C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k2_tarski(k4_tarski(A_6,B_7),k4_tarski(A_6,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_322,plain,(
    ! [A_37,C_38,B_39] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_37),C_38),k2_zfmisc_1(k1_tarski(B_39),C_38)) = k2_zfmisc_1(k2_tarski(A_37,B_39),C_38) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2823,plain,(
    ! [A_141,B_142,C_143,A_144] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_141),k2_tarski(B_142,C_143)),k2_tarski(k4_tarski(A_144,B_142),k4_tarski(A_144,C_143))) = k2_zfmisc_1(k2_tarski(A_141,A_144),k2_tarski(B_142,C_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_322])).

tff(c_2868,plain,(
    ! [A_23,B_24,C_25,A_144] : k2_enumset1(k4_tarski(A_23,B_24),k4_tarski(A_23,C_25),k4_tarski(A_144,B_24),k4_tarski(A_144,C_25)) = k2_zfmisc_1(k2_tarski(A_23,A_144),k2_tarski(B_24,C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_2823])).

tff(c_14,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_14])).

%------------------------------------------------------------------------------
