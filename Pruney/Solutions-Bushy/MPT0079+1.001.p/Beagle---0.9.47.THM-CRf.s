%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:41 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 119 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 139 expanded)
%              Number of equality atoms :   44 (  98 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_18,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_391,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)) = k3_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1708,plain,(
    ! [B_64,A_65,C_66] : k2_xboole_0(k3_xboole_0(B_64,A_65),k3_xboole_0(A_65,C_66)) = k3_xboole_0(A_65,k2_xboole_0(B_64,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_391])).

tff(c_1845,plain,(
    ! [B_64] : k3_xboole_0('#skF_3',k2_xboole_0(B_64,'#skF_1')) = k2_xboole_0(k3_xboole_0(B_64,'#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_1708])).

tff(c_3306,plain,(
    ! [B_82] : k3_xboole_0('#skF_3',k2_xboole_0(B_82,'#skF_1')) = k3_xboole_0(B_82,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1845])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_239,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_263,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_16,c_239])).

tff(c_35,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_35])).

tff(c_262,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_38,c_239])).

tff(c_439,plain,(
    ! [A_7,C_40] : k3_xboole_0(A_7,k2_xboole_0(A_7,C_40)) = k2_xboole_0(A_7,k3_xboole_0(A_7,C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_391])).

tff(c_567,plain,(
    ! [A_43,C_44] : k2_xboole_0(A_43,k3_xboole_0(A_43,C_44)) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_439])).

tff(c_629,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_567])).

tff(c_73,plain,(
    ! [B_21,A_22] : k2_xboole_0(B_21,A_22) = k2_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [A_22,B_21] : r1_tarski(A_22,k2_xboole_0(B_21,A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_16])).

tff(c_259,plain,(
    ! [A_22,B_21] : k3_xboole_0(A_22,k2_xboole_0(B_21,A_22)) = A_22 ),
    inference(resolution,[status(thm)],[c_88,c_239])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_95,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_451,plain,(
    ! [C_40] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_40)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_391])).

tff(c_2386,plain,(
    ! [C_73] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_73)) = k3_xboole_0('#skF_3',C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_451])).

tff(c_2454,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_2386])).

tff(c_2483,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_2454])).

tff(c_2636,plain,(
    ! [B_74,B_75,A_76] : k2_xboole_0(k3_xboole_0(B_74,B_75),k3_xboole_0(A_76,B_74)) = k3_xboole_0(B_74,k2_xboole_0(B_75,A_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_391])).

tff(c_2692,plain,(
    ! [A_76] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_2',A_76)) = k2_xboole_0('#skF_3',k3_xboole_0(A_76,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_2636])).

tff(c_2852,plain,(
    ! [A_76] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_2',A_76)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_2692])).

tff(c_3313,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3306,c_2852])).

tff(c_20,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_184,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_177])).

tff(c_1848,plain,(
    ! [C_66] : k3_xboole_0('#skF_2',k2_xboole_0('#skF_4',C_66)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2',C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_1708])).

tff(c_5041,plain,(
    ! [C_99] : k3_xboole_0('#skF_2',k2_xboole_0('#skF_4',C_99)) = k3_xboole_0('#skF_2',C_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1848])).

tff(c_495,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k2_xboole_0(B_42,A_41)) = A_41 ),
    inference(resolution,[status(thm)],[c_88,c_239])).

tff(c_529,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_495])).

tff(c_5096,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5041,c_529])).

tff(c_5160,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_5096])).

tff(c_5162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_5160])).

%------------------------------------------------------------------------------
