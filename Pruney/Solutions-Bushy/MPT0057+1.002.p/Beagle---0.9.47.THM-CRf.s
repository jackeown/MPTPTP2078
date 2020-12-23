%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0057+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 25.90s
% Output     : CNFRefutation 25.90s
% Verified   : 
% Statistics : Number of formulae       :   44 (  77 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  72 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_167,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k3_xboole_0(A_34,B_35),C_36) = k3_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_670,plain,(
    ! [B_54,A_55,C_56] : k4_xboole_0(k3_xboole_0(B_54,A_55),C_56) = k3_xboole_0(A_55,k4_xboole_0(B_54,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_167])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_698,plain,(
    ! [B_54,A_55,C_56] : k3_xboole_0(B_54,k4_xboole_0(A_55,C_56)) = k3_xboole_0(A_55,k4_xboole_0(B_54,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_16])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_10,B_11] : k4_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_82])).

tff(c_263,plain,(
    ! [A_39,B_40,C_41] : k2_xboole_0(k4_xboole_0(A_39,B_40),k4_xboole_0(A_39,C_41)) = k4_xboole_0(A_39,k3_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_287,plain,(
    ! [A_10,B_11,B_40] : k4_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(B_40,A_10)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(A_10,B_11),B_40),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_263])).

tff(c_301,plain,(
    ! [A_10,B_11,B_40] : k4_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(B_40,A_10)) = k3_xboole_0(A_10,k4_xboole_0(B_11,B_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_287])).

tff(c_284,plain,(
    ! [A_10,B_11,C_41] : k4_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_41)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(A_10,B_11),C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_263])).

tff(c_10770,plain,(
    ! [A_192,B_193,C_194] : k4_xboole_0(k3_xboole_0(A_192,B_193),k3_xboole_0(A_192,C_194)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_192,k4_xboole_0(B_193,C_194))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_284])).

tff(c_11122,plain,(
    ! [A_1,B_193,B_2] : k4_xboole_0(k3_xboole_0(A_1,B_193),k3_xboole_0(B_2,A_1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_1,k4_xboole_0(B_193,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10770])).

tff(c_11209,plain,(
    ! [A_1,B_193,B_2] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_1,k4_xboole_0(B_193,B_2))) = k3_xboole_0(A_1,k4_xboole_0(B_193,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_11122])).

tff(c_178,plain,(
    ! [C_36,B_35] : k3_xboole_0(C_36,k4_xboole_0(B_35,C_36)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_90])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k4_xboole_0(A_7,B_8),k4_xboole_0(A_7,C_9)) = k4_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_695,plain,(
    ! [B_54,A_55,B_8,C_56] : k2_xboole_0(k4_xboole_0(k3_xboole_0(B_54,A_55),B_8),k3_xboole_0(A_55,k4_xboole_0(B_54,C_56))) = k4_xboole_0(k3_xboole_0(B_54,A_55),k3_xboole_0(B_8,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_10])).

tff(c_20474,plain,(
    ! [B_264,A_265,B_266,C_267] : k2_xboole_0(k3_xboole_0(B_264,k4_xboole_0(A_265,B_266)),k3_xboole_0(A_265,k4_xboole_0(B_264,C_267))) = k3_xboole_0(B_264,k4_xboole_0(A_265,k3_xboole_0(B_266,C_267))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_695])).

tff(c_20739,plain,(
    ! [C_36,B_35,C_267] : k3_xboole_0(C_36,k4_xboole_0(B_35,k3_xboole_0(C_36,C_267))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_35,k4_xboole_0(C_36,C_267))) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_20474])).

tff(c_105164,plain,(
    ! [C_36,B_35,C_267] : k3_xboole_0(C_36,k4_xboole_0(B_35,k3_xboole_0(C_36,C_267))) = k3_xboole_0(B_35,k4_xboole_0(C_36,C_267)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11209,c_20739])).

tff(c_18,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_105165,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105164,c_19])).

tff(c_105168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_105165])).

%------------------------------------------------------------------------------
