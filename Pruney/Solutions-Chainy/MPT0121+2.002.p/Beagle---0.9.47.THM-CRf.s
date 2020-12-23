%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:33 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 209 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :   87 ( 248 expanded)
%              Number of equality atoms :   63 ( 168 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_111,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    k3_xboole_0('#skF_4','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_111])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_188,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_18])).

tff(c_191,plain,(
    k4_xboole_0('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_434,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_472,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_434])).

tff(c_482,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_472])).

tff(c_305,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_344,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_305])).

tff(c_357,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_344])).

tff(c_358,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_344])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_366,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = k2_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_22])).

tff(c_483,plain,(
    ! [A_37] : k2_xboole_0(A_37,A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_366])).

tff(c_533,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1464,plain,(
    ! [A_66,C_67] : k4_xboole_0(A_66,k2_xboole_0(A_66,C_67)) = k4_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_533])).

tff(c_1518,plain,(
    ! [A_37] : k4_xboole_0(k1_xboole_0,A_37) = k4_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_1464])).

tff(c_1537,plain,(
    ! [A_68] : k4_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_1518])).

tff(c_1569,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k2_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1537,c_22])).

tff(c_1827,plain,(
    ! [A_72] : k2_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_1569])).

tff(c_1875,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1827])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_135,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_602,plain,(
    ! [A_14,B_15,C_46] : k4_xboole_0(A_14,k2_xboole_0(k3_xboole_0(A_14,B_15),C_46)) = k4_xboole_0(k4_xboole_0(A_14,B_15),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_533])).

tff(c_1997,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(A_75,k2_xboole_0(k3_xboole_0(A_75,B_76),C_77)) = k4_xboole_0(A_75,k2_xboole_0(B_76,C_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_602])).

tff(c_2066,plain,(
    ! [C_77] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,C_77)) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1997])).

tff(c_2106,plain,(
    ! [C_77] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_77)) = k4_xboole_0('#skF_4',C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_2066])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6053,plain,(
    ! [A_132,B_133,C_134] : k4_xboole_0(k4_xboole_0(A_132,B_133),k4_xboole_0(A_132,k2_xboole_0(B_133,C_134))) = k3_xboole_0(k4_xboole_0(A_132,B_133),C_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_20])).

tff(c_6265,plain,(
    ! [A_132,A_37] : k4_xboole_0(k4_xboole_0(A_132,A_37),k4_xboole_0(A_132,A_37)) = k3_xboole_0(k4_xboole_0(A_132,A_37),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_6053])).

tff(c_6369,plain,(
    ! [A_132,A_37] : k3_xboole_0(k4_xboole_0(A_132,A_37),A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_6265])).

tff(c_103,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_651,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,A_49)
      | k3_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_103,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8876,plain,(
    ! [B_158,A_159] :
      ( k3_xboole_0(B_158,A_159) = k1_xboole_0
      | k3_xboole_0(A_159,B_158) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_651,c_4])).

tff(c_8991,plain,(
    ! [A_160,A_161] : k3_xboole_0(A_160,k4_xboole_0(A_161,A_160)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6369,c_8876])).

tff(c_17536,plain,(
    ! [C_223] : k3_xboole_0(k2_xboole_0('#skF_2',C_223),k4_xboole_0('#skF_4',C_223)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2106,c_8991])).

tff(c_17696,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_1'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_17536])).

tff(c_17740,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17696])).

tff(c_660,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(B_48,A_49) = k1_xboole_0
      | k3_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_651,c_4])).

tff(c_17880,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17740,c_660])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_48])).

tff(c_136,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_111])).

tff(c_196,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_18])).

tff(c_199,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_196])).

tff(c_6278,plain,(
    ! [C_134] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_134))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_3'),C_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_6053])).

tff(c_6373,plain,(
    ! [C_134] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_134)) = k3_xboole_0('#skF_4',C_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_199,c_6278])).

tff(c_24,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_661,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_651,c_31])).

tff(c_26243,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6373,c_661])).

tff(c_26246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17880,c_26243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/4.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/4.16  
% 10.01/4.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/4.16  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.01/4.16  
% 10.01/4.16  %Foreground sorts:
% 10.01/4.16  
% 10.01/4.16  
% 10.01/4.16  %Background operators:
% 10.01/4.16  
% 10.01/4.16  
% 10.01/4.16  %Foreground operators:
% 10.01/4.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/4.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.01/4.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.01/4.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.01/4.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.01/4.16  tff('#skF_2', type, '#skF_2': $i).
% 10.01/4.16  tff('#skF_3', type, '#skF_3': $i).
% 10.01/4.16  tff('#skF_1', type, '#skF_1': $i).
% 10.01/4.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/4.16  tff('#skF_4', type, '#skF_4': $i).
% 10.01/4.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/4.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.01/4.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.01/4.16  
% 10.01/4.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.01/4.18  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.01/4.18  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_xboole_1)).
% 10.01/4.18  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.01/4.18  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.01/4.18  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.01/4.18  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 10.01/4.18  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.01/4.18  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.01/4.18  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.01/4.18  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.01/4.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.01/4.18  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/4.18  tff(c_30, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/4.18  tff(c_48, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.01/4.18  tff(c_57, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_48])).
% 10.01/4.18  tff(c_111, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/4.18  tff(c_134, plain, (k3_xboole_0('#skF_4', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_111])).
% 10.01/4.18  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/4.18  tff(c_188, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_18])).
% 10.01/4.18  tff(c_191, plain, (k4_xboole_0('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 10.01/4.18  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/4.18  tff(c_434, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/4.18  tff(c_472, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_434])).
% 10.01/4.18  tff(c_482, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_472])).
% 10.01/4.18  tff(c_305, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.01/4.18  tff(c_344, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_305])).
% 10.01/4.18  tff(c_357, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_344])).
% 10.01/4.18  tff(c_358, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_344])).
% 10.01/4.18  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.01/4.18  tff(c_366, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=k2_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_358, c_22])).
% 10.01/4.18  tff(c_483, plain, (![A_37]: (k2_xboole_0(A_37, A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_482, c_366])).
% 10.01/4.18  tff(c_533, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.18  tff(c_1464, plain, (![A_66, C_67]: (k4_xboole_0(A_66, k2_xboole_0(A_66, C_67))=k4_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_357, c_533])).
% 10.01/4.18  tff(c_1518, plain, (![A_37]: (k4_xboole_0(k1_xboole_0, A_37)=k4_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_483, c_1464])).
% 10.01/4.18  tff(c_1537, plain, (![A_68]: (k4_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_1518])).
% 10.01/4.18  tff(c_1569, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k2_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1537, c_22])).
% 10.01/4.18  tff(c_1827, plain, (![A_72]: (k2_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_482, c_1569])).
% 10.01/4.18  tff(c_1875, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1827])).
% 10.01/4.18  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/4.18  tff(c_56, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_48])).
% 10.01/4.18  tff(c_135, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_111])).
% 10.01/4.18  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.18  tff(c_602, plain, (![A_14, B_15, C_46]: (k4_xboole_0(A_14, k2_xboole_0(k3_xboole_0(A_14, B_15), C_46))=k4_xboole_0(k4_xboole_0(A_14, B_15), C_46))), inference(superposition, [status(thm), theory('equality')], [c_18, c_533])).
% 10.01/4.18  tff(c_1997, plain, (![A_75, B_76, C_77]: (k4_xboole_0(A_75, k2_xboole_0(k3_xboole_0(A_75, B_76), C_77))=k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_602])).
% 10.01/4.18  tff(c_2066, plain, (![C_77]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, C_77))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_77)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1997])).
% 10.01/4.18  tff(c_2106, plain, (![C_77]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_77))=k4_xboole_0('#skF_4', C_77))), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_2066])).
% 10.01/4.18  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.01/4.18  tff(c_6053, plain, (![A_132, B_133, C_134]: (k4_xboole_0(k4_xboole_0(A_132, B_133), k4_xboole_0(A_132, k2_xboole_0(B_133, C_134)))=k3_xboole_0(k4_xboole_0(A_132, B_133), C_134))), inference(superposition, [status(thm), theory('equality')], [c_533, c_20])).
% 10.01/4.18  tff(c_6265, plain, (![A_132, A_37]: (k4_xboole_0(k4_xboole_0(A_132, A_37), k4_xboole_0(A_132, A_37))=k3_xboole_0(k4_xboole_0(A_132, A_37), A_37))), inference(superposition, [status(thm), theory('equality')], [c_483, c_6053])).
% 10.01/4.18  tff(c_6369, plain, (![A_132, A_37]: (k3_xboole_0(k4_xboole_0(A_132, A_37), A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_6265])).
% 10.01/4.18  tff(c_103, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/4.18  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.01/4.18  tff(c_651, plain, (![B_48, A_49]: (r1_xboole_0(B_48, A_49) | k3_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_8])).
% 10.01/4.18  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/4.18  tff(c_8876, plain, (![B_158, A_159]: (k3_xboole_0(B_158, A_159)=k1_xboole_0 | k3_xboole_0(A_159, B_158)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_651, c_4])).
% 10.01/4.18  tff(c_8991, plain, (![A_160, A_161]: (k3_xboole_0(A_160, k4_xboole_0(A_161, A_160))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6369, c_8876])).
% 10.01/4.18  tff(c_17536, plain, (![C_223]: (k3_xboole_0(k2_xboole_0('#skF_2', C_223), k4_xboole_0('#skF_4', C_223))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2106, c_8991])).
% 10.01/4.18  tff(c_17696, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_1'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_191, c_17536])).
% 10.01/4.18  tff(c_17740, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17696])).
% 10.01/4.18  tff(c_660, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k1_xboole_0 | k3_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_651, c_4])).
% 10.01/4.18  tff(c_17880, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_17740, c_660])).
% 10.01/4.18  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/4.18  tff(c_55, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_48])).
% 10.01/4.18  tff(c_136, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_111])).
% 10.01/4.18  tff(c_196, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_136, c_18])).
% 10.01/4.18  tff(c_199, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_196])).
% 10.01/4.18  tff(c_6278, plain, (![C_134]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_134)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_3'), C_134))), inference(superposition, [status(thm), theory('equality')], [c_199, c_6053])).
% 10.01/4.18  tff(c_6373, plain, (![C_134]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_134))=k3_xboole_0('#skF_4', C_134))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_199, c_6278])).
% 10.01/4.18  tff(c_24, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/4.18  tff(c_31, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 10.01/4.18  tff(c_661, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_651, c_31])).
% 10.01/4.18  tff(c_26243, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6373, c_661])).
% 10.01/4.18  tff(c_26246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17880, c_26243])).
% 10.01/4.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/4.18  
% 10.01/4.18  Inference rules
% 10.01/4.18  ----------------------
% 10.01/4.18  #Ref     : 0
% 10.01/4.18  #Sup     : 6550
% 10.01/4.18  #Fact    : 0
% 10.01/4.18  #Define  : 0
% 10.01/4.18  #Split   : 0
% 10.01/4.18  #Chain   : 0
% 10.01/4.18  #Close   : 0
% 10.01/4.18  
% 10.01/4.18  Ordering : KBO
% 10.01/4.18  
% 10.01/4.18  Simplification rules
% 10.01/4.18  ----------------------
% 10.01/4.18  #Subsume      : 7
% 10.01/4.18  #Demod        : 7290
% 10.01/4.18  #Tautology    : 4650
% 10.01/4.18  #SimpNegUnit  : 0
% 10.01/4.18  #BackRed      : 15
% 10.01/4.18  
% 10.01/4.18  #Partial instantiations: 0
% 10.01/4.18  #Strategies tried      : 1
% 10.01/4.18  
% 10.01/4.18  Timing (in seconds)
% 10.01/4.18  ----------------------
% 10.01/4.18  Preprocessing        : 0.27
% 10.01/4.18  Parsing              : 0.15
% 10.01/4.18  CNF conversion       : 0.02
% 10.01/4.18  Main loop            : 3.15
% 10.01/4.18  Inferencing          : 0.61
% 10.01/4.18  Reduction            : 1.84
% 10.01/4.18  Demodulation         : 1.64
% 10.01/4.18  BG Simplification    : 0.07
% 10.01/4.18  Subsumption          : 0.49
% 10.01/4.18  Abstraction          : 0.11
% 10.01/4.18  MUC search           : 0.00
% 10.01/4.18  Cooper               : 0.00
% 10.01/4.18  Total                : 3.45
% 10.01/4.18  Index Insertion      : 0.00
% 10.01/4.18  Index Deletion       : 0.00
% 10.01/4.18  Index Matching       : 0.00
% 10.01/4.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
