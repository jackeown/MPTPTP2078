%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0102+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:43 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  59 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_34,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k3_xboole_0(A_7,B_8),k5_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_354,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),k4_xboole_0(B_55,A_54)) = k5_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1444,plain,(
    ! [B_95,A_96] : k2_xboole_0(k4_xboole_0(B_95,A_96),k4_xboole_0(A_96,B_95)) = k5_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1483,plain,(
    ! [B_95,A_96] : k5_xboole_0(B_95,A_96) = k5_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_1444,c_4])).

tff(c_236,plain,(
    ! [A_38,B_39] : k2_xboole_0(k5_xboole_0(A_38,B_39),k3_xboole_0(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_248,plain,(
    ! [A_38,B_39] : k2_xboole_0(k3_xboole_0(A_38,B_39),k5_xboole_0(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_293,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k3_xboole_0(A_48,B_49)) = k5_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_504,plain,(
    ! [A_56,B_57] : r1_tarski(k5_xboole_0(A_56,B_57),k2_xboole_0(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_16])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_529,plain,(
    ! [A_56,B_57] : k4_xboole_0(k5_xboole_0(A_56,B_57),k2_xboole_0(A_56,B_57)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_504,c_8])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(k2_xboole_0(A_14,B_15),B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_402,plain,(
    ! [B_15,A_14] :
      ( k2_xboole_0(k4_xboole_0(B_15,k2_xboole_0(A_14,B_15)),A_14) = k5_xboole_0(B_15,k2_xboole_0(A_14,B_15))
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_354])).

tff(c_2800,plain,(
    ! [A_126,B_127] :
      ( k2_xboole_0(A_126,k4_xboole_0(B_127,k2_xboole_0(A_126,B_127))) = k5_xboole_0(B_127,k2_xboole_0(A_126,B_127))
      | ~ r1_xboole_0(A_126,B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402])).

tff(c_2870,plain,(
    ! [A_38,B_39] :
      ( k5_xboole_0(k5_xboole_0(A_38,B_39),k2_xboole_0(k3_xboole_0(A_38,B_39),k5_xboole_0(A_38,B_39))) = k2_xboole_0(k3_xboole_0(A_38,B_39),k4_xboole_0(k5_xboole_0(A_38,B_39),k2_xboole_0(A_38,B_39)))
      | ~ r1_xboole_0(k3_xboole_0(A_38,B_39),k5_xboole_0(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2800])).

tff(c_2910,plain,(
    ! [A_38,B_39] : k5_xboole_0(k2_xboole_0(A_38,B_39),k5_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1483,c_248,c_14,c_529,c_2870])).

tff(c_22,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1656,plain,(
    k5_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_22])).

tff(c_8396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2910,c_1656])).

%------------------------------------------------------------------------------
