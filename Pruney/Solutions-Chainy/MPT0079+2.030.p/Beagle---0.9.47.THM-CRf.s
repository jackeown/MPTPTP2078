%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:46 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 252 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 289 expanded)
%              Number of equality atoms :   91 ( 244 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_36,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_160])).

tff(c_193,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_205,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_193])).

tff(c_212,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_205])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_783,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k4_xboole_0(A_68,B_69),C_70) = k4_xboole_0(A_68,k2_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_246,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_222])).

tff(c_254,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_805,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k2_xboole_0(B_69,k4_xboole_0(A_68,B_69))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_254])).

tff(c_897,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k2_xboole_0(B_72,A_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_805])).

tff(c_1408,plain,(
    ! [A_84,B_85] : k4_xboole_0(k4_xboole_0(A_84,B_85),A_84) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_897])).

tff(c_1431,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = k2_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1408,c_18])).

tff(c_1509,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1431])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_28,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_260,plain,(
    ! [A_51] : k4_xboole_0(A_51,k1_xboole_0) = k3_xboole_0(A_51,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_28])).

tff(c_272,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_260])).

tff(c_1821,plain,(
    ! [A_90,B_91,C_92] : k2_xboole_0(k4_xboole_0(A_90,B_91),k3_xboole_0(A_90,C_92)) = k4_xboole_0(A_90,k4_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1911,plain,(
    ! [A_51,B_91] : k4_xboole_0(A_51,k4_xboole_0(B_91,A_51)) = k2_xboole_0(k4_xboole_0(A_51,B_91),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_1821])).

tff(c_3035,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(B_104,A_103)) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_2,c_1911])).

tff(c_3200,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_3035])).

tff(c_1932,plain,(
    ! [B_91] : k4_xboole_0('#skF_4',k4_xboole_0(B_91,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_4',B_91),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1821])).

tff(c_1966,plain,(
    ! [B_91] : k4_xboole_0('#skF_4',k4_xboole_0(B_91,'#skF_2')) = k4_xboole_0('#skF_4',B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1932])).

tff(c_69,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_35] : k2_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_299,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_318,plain,(
    ! [A_35] : k4_xboole_0(k1_xboole_0,A_35) = k4_xboole_0(A_35,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_299])).

tff(c_335,plain,(
    ! [A_35] : k4_xboole_0(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_318])).

tff(c_844,plain,(
    ! [A_13,C_70] : k4_xboole_0(A_13,k2_xboole_0(A_13,C_70)) = k4_xboole_0(k1_xboole_0,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_783])).

tff(c_890,plain,(
    ! [A_13,C_70] : k4_xboole_0(A_13,k2_xboole_0(A_13,C_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_844])).

tff(c_42,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_315,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_299])).

tff(c_2421,plain,(
    ! [B_98] : k4_xboole_0('#skF_4',k4_xboole_0(B_98,'#skF_2')) = k4_xboole_0('#skF_4',B_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1932])).

tff(c_2483,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_2421])).

tff(c_2518,plain,(
    k4_xboole_0('#skF_4','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_890,c_2483])).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_168,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_160])).

tff(c_1929,plain,(
    ! [B_91] : k4_xboole_0('#skF_3',k4_xboole_0(B_91,'#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_3',B_91),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_1821])).

tff(c_1965,plain,(
    ! [B_91] : k4_xboole_0('#skF_3',k4_xboole_0(B_91,'#skF_1')) = k4_xboole_0('#skF_3',B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1929])).

tff(c_2527,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_1965])).

tff(c_2560,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2527])).

tff(c_321,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_879,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k2_xboole_0(B_69,A_68)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_805])).

tff(c_581,plain,(
    ! [B_62,A_63] : k4_xboole_0(k2_xboole_0(B_62,A_63),B_62) = k4_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_620,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_581])).

tff(c_2064,plain,(
    ! [B_95] : k4_xboole_0('#skF_3',k4_xboole_0(B_95,'#skF_1')) = k4_xboole_0('#skF_3',B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1929])).

tff(c_2119,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_1')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_2064])).

tff(c_2156,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_879,c_2119])).

tff(c_184,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | k4_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | k4_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_184,c_12])).

tff(c_2201,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_191])).

tff(c_1302,plain,(
    ! [A_81,B_82,C_83] : k2_xboole_0(k2_xboole_0(A_81,B_82),C_83) = k2_xboole_0(A_81,k2_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1387,plain,(
    ! [A_81,B_82,A_1] : k2_xboole_0(A_81,k2_xboole_0(B_82,A_1)) = k2_xboole_0(A_1,k2_xboole_0(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1302])).

tff(c_3884,plain,(
    ! [A_113,A_111,B_112] : k2_xboole_0(A_113,k2_xboole_0(A_111,B_112)) = k2_xboole_0(A_111,k2_xboole_0(B_112,A_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1302])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(k2_xboole_0(A_14,B_15),B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_425,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_447,plain,(
    ! [B_15,A_14] : k2_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = k2_xboole_0(B_15,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_425])).

tff(c_3248,plain,(
    ! [B_105,A_106] : k2_xboole_0(B_105,k2_xboole_0(A_106,B_105)) = k2_xboole_0(B_105,A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_447])).

tff(c_3330,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_3248])).

tff(c_3368,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_2,c_3330])).

tff(c_3927,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3884,c_3368])).

tff(c_4244,plain,(
    k2_xboole_0('#skF_4','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2201,c_2,c_1387,c_2,c_3927])).

tff(c_4307,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4244,c_321])).

tff(c_4319,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3200,c_2560,c_321,c_4307])).

tff(c_4321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_4319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.89  
% 4.61/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.89  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.61/1.89  
% 4.61/1.89  %Foreground sorts:
% 4.61/1.89  
% 4.61/1.89  
% 4.61/1.89  %Background operators:
% 4.61/1.89  
% 4.61/1.89  
% 4.61/1.89  %Foreground operators:
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.61/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.89  
% 4.61/1.91  tff(f_70, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.61/1.91  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.61/1.91  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.61/1.91  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.61/1.91  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.61/1.91  tff(f_59, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.61/1.91  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.61/1.91  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.61/1.91  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.61/1.91  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.61/1.91  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.61/1.91  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.61/1.91  tff(f_49, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.61/1.91  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.61/1.91  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.61/1.91  tff(f_57, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.61/1.91  tff(c_36, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.61/1.91  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.61/1.91  tff(c_38, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.61/1.91  tff(c_160, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.91  tff(c_167, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_160])).
% 4.61/1.91  tff(c_193, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.61/1.91  tff(c_205, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_193])).
% 4.61/1.91  tff(c_212, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_205])).
% 4.61/1.91  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.91  tff(c_32, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.61/1.91  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.91  tff(c_783, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k4_xboole_0(A_68, B_69), C_70)=k4_xboole_0(A_68, k2_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.91  tff(c_16, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.61/1.91  tff(c_222, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.61/1.91  tff(c_246, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_222])).
% 4.61/1.91  tff(c_254, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_246])).
% 4.61/1.91  tff(c_805, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k2_xboole_0(B_69, k4_xboole_0(A_68, B_69)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_783, c_254])).
% 4.61/1.91  tff(c_897, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k2_xboole_0(B_72, A_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_805])).
% 4.61/1.91  tff(c_1408, plain, (![A_84, B_85]: (k4_xboole_0(k4_xboole_0(A_84, B_85), A_84)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_897])).
% 4.61/1.91  tff(c_1431, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k4_xboole_0(A_84, B_85))=k2_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1408, c_18])).
% 4.61/1.91  tff(c_1509, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k4_xboole_0(A_84, B_85))=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1431])).
% 4.61/1.91  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.91  tff(c_255, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_246])).
% 4.61/1.91  tff(c_28, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.61/1.91  tff(c_260, plain, (![A_51]: (k4_xboole_0(A_51, k1_xboole_0)=k3_xboole_0(A_51, A_51))), inference(superposition, [status(thm), theory('equality')], [c_255, c_28])).
% 4.61/1.91  tff(c_272, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_260])).
% 4.61/1.91  tff(c_1821, plain, (![A_90, B_91, C_92]: (k2_xboole_0(k4_xboole_0(A_90, B_91), k3_xboole_0(A_90, C_92))=k4_xboole_0(A_90, k4_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.61/1.91  tff(c_1911, plain, (![A_51, B_91]: (k4_xboole_0(A_51, k4_xboole_0(B_91, A_51))=k2_xboole_0(k4_xboole_0(A_51, B_91), A_51))), inference(superposition, [status(thm), theory('equality')], [c_272, c_1821])).
% 4.61/1.91  tff(c_3035, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(B_104, A_103))=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_2, c_1911])).
% 4.61/1.91  tff(c_3200, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_212, c_3035])).
% 4.61/1.91  tff(c_1932, plain, (![B_91]: (k4_xboole_0('#skF_4', k4_xboole_0(B_91, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_4', B_91), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_167, c_1821])).
% 4.61/1.91  tff(c_1966, plain, (![B_91]: (k4_xboole_0('#skF_4', k4_xboole_0(B_91, '#skF_2'))=k4_xboole_0('#skF_4', B_91))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1932])).
% 4.61/1.91  tff(c_69, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.91  tff(c_85, plain, (![A_35]: (k2_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_69, c_14])).
% 4.61/1.91  tff(c_299, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.91  tff(c_318, plain, (![A_35]: (k4_xboole_0(k1_xboole_0, A_35)=k4_xboole_0(A_35, A_35))), inference(superposition, [status(thm), theory('equality')], [c_85, c_299])).
% 4.61/1.91  tff(c_335, plain, (![A_35]: (k4_xboole_0(k1_xboole_0, A_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_254, c_318])).
% 4.61/1.91  tff(c_844, plain, (![A_13, C_70]: (k4_xboole_0(A_13, k2_xboole_0(A_13, C_70))=k4_xboole_0(k1_xboole_0, C_70))), inference(superposition, [status(thm), theory('equality')], [c_254, c_783])).
% 4.61/1.91  tff(c_890, plain, (![A_13, C_70]: (k4_xboole_0(A_13, k2_xboole_0(A_13, C_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_335, c_844])).
% 4.61/1.91  tff(c_42, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.61/1.91  tff(c_43, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 4.61/1.91  tff(c_315, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_43, c_299])).
% 4.61/1.91  tff(c_2421, plain, (![B_98]: (k4_xboole_0('#skF_4', k4_xboole_0(B_98, '#skF_2'))=k4_xboole_0('#skF_4', B_98))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1932])).
% 4.61/1.91  tff(c_2483, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_315, c_2421])).
% 4.61/1.91  tff(c_2518, plain, (k4_xboole_0('#skF_4', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_890, c_2483])).
% 4.61/1.91  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.61/1.91  tff(c_168, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_160])).
% 4.61/1.91  tff(c_1929, plain, (![B_91]: (k4_xboole_0('#skF_3', k4_xboole_0(B_91, '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_3', B_91), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_1821])).
% 4.61/1.91  tff(c_1965, plain, (![B_91]: (k4_xboole_0('#skF_3', k4_xboole_0(B_91, '#skF_1'))=k4_xboole_0('#skF_3', B_91))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1929])).
% 4.61/1.91  tff(c_2527, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2518, c_1965])).
% 4.61/1.91  tff(c_2560, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2527])).
% 4.61/1.91  tff(c_321, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_299])).
% 4.61/1.91  tff(c_879, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k2_xboole_0(B_69, A_68))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_805])).
% 4.61/1.91  tff(c_581, plain, (![B_62, A_63]: (k4_xboole_0(k2_xboole_0(B_62, A_63), B_62)=k4_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_299])).
% 4.61/1.91  tff(c_620, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_581])).
% 4.61/1.91  tff(c_2064, plain, (![B_95]: (k4_xboole_0('#skF_3', k4_xboole_0(B_95, '#skF_1'))=k4_xboole_0('#skF_3', B_95))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1929])).
% 4.61/1.91  tff(c_2119, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_620, c_2064])).
% 4.61/1.91  tff(c_2156, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_879, c_2119])).
% 4.61/1.91  tff(c_184, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | k4_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.61/1.91  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.61/1.91  tff(c_191, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | k4_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_184, c_12])).
% 4.61/1.91  tff(c_2201, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2156, c_191])).
% 4.61/1.91  tff(c_1302, plain, (![A_81, B_82, C_83]: (k2_xboole_0(k2_xboole_0(A_81, B_82), C_83)=k2_xboole_0(A_81, k2_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.61/1.91  tff(c_1387, plain, (![A_81, B_82, A_1]: (k2_xboole_0(A_81, k2_xboole_0(B_82, A_1))=k2_xboole_0(A_1, k2_xboole_0(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1302])).
% 4.61/1.91  tff(c_3884, plain, (![A_113, A_111, B_112]: (k2_xboole_0(A_113, k2_xboole_0(A_111, B_112))=k2_xboole_0(A_111, k2_xboole_0(B_112, A_113)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1302])).
% 4.61/1.91  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(k2_xboole_0(A_14, B_15), B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.91  tff(c_425, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.91  tff(c_447, plain, (![B_15, A_14]: (k2_xboole_0(B_15, k4_xboole_0(A_14, B_15))=k2_xboole_0(B_15, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_425])).
% 4.61/1.91  tff(c_3248, plain, (![B_105, A_106]: (k2_xboole_0(B_105, k2_xboole_0(A_106, B_105))=k2_xboole_0(B_105, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_447])).
% 4.61/1.91  tff(c_3330, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_3248])).
% 4.61/1.91  tff(c_3368, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_2, c_3330])).
% 4.61/1.91  tff(c_3927, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3884, c_3368])).
% 4.61/1.91  tff(c_4244, plain, (k2_xboole_0('#skF_4', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2201, c_2, c_1387, c_2, c_3927])).
% 4.61/1.91  tff(c_4307, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4244, c_321])).
% 4.61/1.91  tff(c_4319, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3200, c_2560, c_321, c_4307])).
% 4.61/1.91  tff(c_4321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_4319])).
% 4.61/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.91  
% 4.61/1.91  Inference rules
% 4.61/1.91  ----------------------
% 4.61/1.91  #Ref     : 0
% 4.61/1.91  #Sup     : 1104
% 4.61/1.91  #Fact    : 0
% 4.61/1.91  #Define  : 0
% 4.61/1.91  #Split   : 2
% 4.61/1.91  #Chain   : 0
% 4.61/1.91  #Close   : 0
% 4.61/1.91  
% 4.61/1.91  Ordering : KBO
% 4.61/1.91  
% 4.61/1.91  Simplification rules
% 4.61/1.91  ----------------------
% 4.61/1.91  #Subsume      : 16
% 4.61/1.91  #Demod        : 890
% 4.61/1.91  #Tautology    : 676
% 4.61/1.91  #SimpNegUnit  : 1
% 4.61/1.91  #BackRed      : 0
% 4.61/1.91  
% 4.61/1.91  #Partial instantiations: 0
% 4.61/1.91  #Strategies tried      : 1
% 4.61/1.91  
% 4.61/1.91  Timing (in seconds)
% 4.61/1.91  ----------------------
% 4.61/1.91  Preprocessing        : 0.32
% 4.61/1.91  Parsing              : 0.18
% 4.61/1.91  CNF conversion       : 0.02
% 4.61/1.91  Main loop            : 0.79
% 4.61/1.91  Inferencing          : 0.25
% 4.61/1.91  Reduction            : 0.36
% 4.61/1.91  Demodulation         : 0.29
% 4.61/1.91  BG Simplification    : 0.03
% 4.61/1.91  Subsumption          : 0.11
% 4.61/1.91  Abstraction          : 0.04
% 4.61/1.91  MUC search           : 0.00
% 4.61/1.91  Cooper               : 0.00
% 4.61/1.91  Total                : 1.15
% 4.61/1.91  Index Insertion      : 0.00
% 4.61/1.91  Index Deletion       : 0.00
% 4.61/1.91  Index Matching       : 0.00
% 4.61/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
