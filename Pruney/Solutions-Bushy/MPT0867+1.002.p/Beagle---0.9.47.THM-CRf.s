%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0867+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:59 EST 2020

% Result     : Theorem 12.71s
% Output     : CNFRefutation 12.71s
% Verified   : 
% Statistics : Number of formulae       :   42 (  78 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  78 expanded)
%              Number of equality atoms :   30 (  77 expanded)
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

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

tff(c_171,plain,(
    ! [A_30,B_31,C_32] : k2_zfmisc_1(k1_tarski(A_30),k2_tarski(B_31,C_32)) = k2_tarski(k4_tarski(A_30,B_31),k4_tarski(A_30,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k2_tarski(A_9,B_10),k2_tarski(C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_199,plain,(
    ! [B_10,A_30,C_32,B_31,A_9] : k2_xboole_0(k2_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(A_30),k2_tarski(B_31,C_32))) = k2_enumset1(A_9,B_10,k4_tarski(A_30,B_31),k4_tarski(A_30,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k2_tarski(k4_tarski(A_6,B_7),k4_tarski(A_6,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_300,plain,(
    ! [A_38,C_39,B_40] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_38),C_39),k2_zfmisc_1(k1_tarski(B_40),C_39)) = k2_zfmisc_1(k2_tarski(A_38,B_40),C_39) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10292,plain,(
    ! [A_203,B_204,C_205,B_206] : k2_xboole_0(k2_tarski(k4_tarski(A_203,B_204),k4_tarski(A_203,C_205)),k2_zfmisc_1(k1_tarski(B_206),k2_tarski(B_204,C_205))) = k2_zfmisc_1(k2_tarski(A_203,B_206),k2_tarski(B_204,C_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_300])).

tff(c_10352,plain,(
    ! [A_203,B_31,C_32,A_30] : k2_enumset1(k4_tarski(A_203,B_31),k4_tarski(A_203,C_32),k4_tarski(A_30,B_31),k4_tarski(A_30,C_32)) = k2_zfmisc_1(k2_tarski(A_203,A_30),k2_tarski(B_31,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_10292])).

tff(c_267,plain,(
    ! [C_35,A_36,B_37] : k2_xboole_0(k2_zfmisc_1(C_35,k1_tarski(A_36)),k2_zfmisc_1(C_35,k1_tarski(B_37))) = k2_zfmisc_1(C_35,k2_tarski(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_341,plain,(
    ! [C_41,B_42,A_43] : k2_xboole_0(k2_zfmisc_1(C_41,k1_tarski(B_42)),k2_zfmisc_1(C_41,k1_tarski(A_43))) = k2_zfmisc_1(C_41,k2_tarski(A_43,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2])).

tff(c_6,plain,(
    ! [C_5,A_3,B_4] : k2_xboole_0(k2_zfmisc_1(C_5,k1_tarski(A_3)),k2_zfmisc_1(C_5,k1_tarski(B_4))) = k2_zfmisc_1(C_5,k2_tarski(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_393,plain,(
    ! [C_44,B_45,A_46] : k2_zfmisc_1(C_44,k2_tarski(B_45,A_46)) = k2_zfmisc_1(C_44,k2_tarski(A_46,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_6])).

tff(c_468,plain,(
    ! [A_47,B_48,A_49] : k2_zfmisc_1(k1_tarski(A_47),k2_tarski(B_48,A_49)) = k2_tarski(k4_tarski(A_47,A_49),k4_tarski(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_8])).

tff(c_12381,plain,(
    ! [B_250,A_253,A_249,C_251,D_252] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_249),k2_tarski(B_250,A_253)),k2_tarski(C_251,D_252)) = k2_enumset1(k4_tarski(A_249,A_253),k4_tarski(A_249,B_250),C_251,D_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_12])).

tff(c_196,plain,(
    ! [C_11,A_30,C_32,B_31,D_12] : k2_xboole_0(k2_zfmisc_1(k1_tarski(A_30),k2_tarski(B_31,C_32)),k2_tarski(C_11,D_12)) = k2_enumset1(k4_tarski(A_30,B_31),k4_tarski(A_30,C_32),C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_12470,plain,(
    ! [B_250,A_253,A_249,C_251,D_252] : k2_enumset1(k4_tarski(A_249,B_250),k4_tarski(A_249,A_253),C_251,D_252) = k2_enumset1(k4_tarski(A_249,A_253),k4_tarski(A_249,B_250),C_251,D_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_12381,c_196])).

tff(c_10671,plain,(
    ! [A_216,B_214,A_215,B_213,A_212] : k2_xboole_0(k2_tarski(A_216,B_214),k2_zfmisc_1(k1_tarski(A_212),k2_tarski(B_213,A_215))) = k2_enumset1(A_216,B_214,k4_tarski(A_212,A_215),k4_tarski(A_212,B_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_12])).

tff(c_10802,plain,(
    ! [B_10,A_30,C_32,B_31,A_9] : k2_enumset1(A_9,B_10,k4_tarski(A_30,C_32),k4_tarski(A_30,B_31)) = k2_enumset1(A_9,B_10,k4_tarski(A_30,B_31),k4_tarski(A_30,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_10671])).

tff(c_351,plain,(
    ! [C_41,B_42,A_43] : k2_zfmisc_1(C_41,k2_tarski(B_42,A_43)) = k2_zfmisc_1(C_41,k2_tarski(A_43,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_6])).

tff(c_14,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_392,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_14])).

tff(c_11696,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_4'),k4_tarski('#skF_2','#skF_3')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10802,c_392])).

tff(c_12701,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_4'),k4_tarski('#skF_2','#skF_3')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12470,c_11696])).

tff(c_15052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10352,c_12701])).

%------------------------------------------------------------------------------
