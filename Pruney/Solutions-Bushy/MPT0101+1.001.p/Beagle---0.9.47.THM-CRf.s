%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0101+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:43 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_26,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(k5_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_25,plain,(
    ! [A_17,B_18] : r1_xboole_0(k3_xboole_0(A_17,B_18),k5_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_17,B_18] : k4_xboole_0(k3_xboole_0(A_17,B_18),k5_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_25,c_8])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_21,B_22] : r1_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_25,c_6])).

tff(c_87,plain,(
    ! [A_31,B_32] : k4_xboole_0(k5_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k5_xboole_0(A_31,B_32) ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_93,plain,(
    ! [A_31,B_32] : k2_xboole_0(k5_xboole_0(A_31,B_32),k4_xboole_0(k3_xboole_0(A_31,B_32),k5_xboole_0(A_31,B_32))) = k5_xboole_0(k5_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_103,plain,(
    ! [A_31,B_32] : k5_xboole_0(k5_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_31,c_93])).

tff(c_14,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_14])).

%------------------------------------------------------------------------------
