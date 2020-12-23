%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 9.36s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 415 expanded)
%              Number of leaves         :   31 ( 155 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 551 expanded)
%              Number of equality atoms :   66 ( 345 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_287,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_342,plain,(
    ! [A_61,B_62] :
      ( ~ r1_xboole_0(A_61,B_62)
      | k3_xboole_0(A_61,B_62) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_287])).

tff(c_349,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_342])).

tff(c_864,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_905,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_864])).

tff(c_924,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_905])).

tff(c_42,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_43,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_67,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [A_41,B_40] : r1_tarski(A_41,k2_xboole_0(B_40,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_34])).

tff(c_122,plain,(
    r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_82])).

tff(c_1668,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_tarski(k4_xboole_0(A_102,B_103),C_104)
      | ~ r1_tarski(A_102,k2_xboole_0(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15921,plain,(
    ! [A_271,B_272,C_273] :
      ( k2_xboole_0(k4_xboole_0(A_271,B_272),C_273) = C_273
      | ~ r1_tarski(A_271,k2_xboole_0(B_272,C_273)) ) ),
    inference(resolution,[status(thm)],[c_1668,c_18])).

tff(c_16158,plain,(
    k2_xboole_0(k4_xboole_0('#skF_6','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_122,c_15921])).

tff(c_16263,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_924,c_16158])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_350,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_342])).

tff(c_442,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_350])).

tff(c_896,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_864])).

tff(c_921,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_896])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(k2_xboole_0(A_21,B_22),B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_661,plain,(
    ! [A_73,B_74] : k4_xboole_0(k2_xboole_0(A_73,B_74),B_74) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_670,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,k4_xboole_0(A_73,B_74)) = k2_xboole_0(B_74,k2_xboole_0(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_20])).

tff(c_705,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,k2_xboole_0(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_670])).

tff(c_1224,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k2_xboole_0(A_87,B_88),C_89) = k2_xboole_0(A_87,k2_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5554,plain,(
    ! [A_175,B_176,C_177] : r1_tarski(k2_xboole_0(A_175,B_176),k2_xboole_0(A_175,k2_xboole_0(B_176,C_177))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_34])).

tff(c_6112,plain,(
    ! [A_185] : r1_tarski(k2_xboole_0(A_185,'#skF_5'),k2_xboole_0(A_185,k2_xboole_0('#skF_4','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_5554])).

tff(c_6122,plain,(
    r1_tarski(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_6112])).

tff(c_6202,plain,(
    r1_tarski(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6122])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_17074,plain,(
    ! [A_274,B_275,C_276] :
      ( k4_xboole_0(k4_xboole_0(A_274,B_275),C_276) = k1_xboole_0
      | ~ r1_tarski(A_274,k2_xboole_0(B_275,C_276)) ) ),
    inference(resolution,[status(thm)],[c_1668,c_16])).

tff(c_17414,plain,(
    ! [A_277] :
      ( k4_xboole_0(k4_xboole_0(A_277,'#skF_5'),'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_277,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_17074])).

tff(c_17458,plain,(
    k4_xboole_0(k4_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6202,c_17414])).

tff(c_17562,plain,(
    k4_xboole_0('#skF_3','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_24,c_17458])).

tff(c_218,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_218])).

tff(c_520,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_547,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_520])).

tff(c_560,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_547])).

tff(c_2091,plain,(
    ! [A_113,B_114] : k4_xboole_0(k2_xboole_0(A_113,B_114),A_113) = k4_xboole_0(B_114,A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_661])).

tff(c_30,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2110,plain,(
    ! [A_113,B_114] : k4_xboole_0(k2_xboole_0(A_113,B_114),k4_xboole_0(B_114,A_113)) = k3_xboole_0(k2_xboole_0(A_113,B_114),A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_2091,c_30])).

tff(c_2162,plain,(
    ! [A_113,B_114] : k4_xboole_0(k2_xboole_0(A_113,B_114),k4_xboole_0(B_114,A_113)) = A_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_4,c_2110])).

tff(c_17622,plain,(
    k4_xboole_0(k2_xboole_0('#skF_6','#skF_3'),k1_xboole_0) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_17562,c_2162])).

tff(c_17678,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16263,c_22,c_2,c_17622])).

tff(c_364,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_349])).

tff(c_899,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_864])).

tff(c_922,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_899])).

tff(c_17731,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17678,c_922])).

tff(c_902,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_864])).

tff(c_923,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_902])).

tff(c_689,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_661])).

tff(c_17733,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17678,c_17678,c_689])).

tff(c_17763,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_24,c_17733])).

tff(c_18526,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17731,c_17763])).

tff(c_18527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_18526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:25:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.36/3.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.36/3.45  
% 9.36/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.36/3.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 9.36/3.45  
% 9.36/3.45  %Foreground sorts:
% 9.36/3.45  
% 9.36/3.45  
% 9.36/3.45  %Background operators:
% 9.36/3.45  
% 9.36/3.45  
% 9.36/3.45  %Foreground operators:
% 9.36/3.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.36/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.36/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.36/3.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.36/3.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.36/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.36/3.45  tff('#skF_5', type, '#skF_5': $i).
% 9.36/3.45  tff('#skF_6', type, '#skF_6': $i).
% 9.36/3.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.36/3.45  tff('#skF_3', type, '#skF_3': $i).
% 9.36/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.36/3.45  tff('#skF_4', type, '#skF_4': $i).
% 9.36/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.36/3.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.36/3.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.36/3.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.36/3.45  
% 9.61/3.47  tff(f_88, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 9.61/3.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.61/3.47  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.61/3.47  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.61/3.47  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.61/3.47  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.61/3.47  tff(f_79, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.61/3.47  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.61/3.47  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.61/3.47  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.61/3.47  tff(f_67, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.61/3.47  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.61/3.47  tff(f_77, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.61/3.47  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.61/3.47  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.61/3.47  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.61/3.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.61/3.47  tff(c_22, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.61/3.47  tff(c_38, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.61/3.47  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.61/3.47  tff(c_287, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.47  tff(c_342, plain, (![A_61, B_62]: (~r1_xboole_0(A_61, B_62) | k3_xboole_0(A_61, B_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_287])).
% 9.61/3.47  tff(c_349, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_342])).
% 9.61/3.47  tff(c_864, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.61/3.47  tff(c_905, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_349, c_864])).
% 9.61/3.47  tff(c_924, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_905])).
% 9.61/3.47  tff(c_42, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.61/3.47  tff(c_43, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 9.61/3.47  tff(c_67, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.61/3.47  tff(c_34, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.61/3.47  tff(c_82, plain, (![A_41, B_40]: (r1_tarski(A_41, k2_xboole_0(B_40, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_34])).
% 9.61/3.47  tff(c_122, plain, (r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_82])).
% 9.61/3.47  tff(c_1668, plain, (![A_102, B_103, C_104]: (r1_tarski(k4_xboole_0(A_102, B_103), C_104) | ~r1_tarski(A_102, k2_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.61/3.47  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.61/3.47  tff(c_15921, plain, (![A_271, B_272, C_273]: (k2_xboole_0(k4_xboole_0(A_271, B_272), C_273)=C_273 | ~r1_tarski(A_271, k2_xboole_0(B_272, C_273)))), inference(resolution, [status(thm)], [c_1668, c_18])).
% 9.61/3.47  tff(c_16158, plain, (k2_xboole_0(k4_xboole_0('#skF_6', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_122, c_15921])).
% 9.61/3.47  tff(c_16263, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_924, c_16158])).
% 9.61/3.47  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.61/3.47  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.61/3.47  tff(c_350, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_342])).
% 9.61/3.47  tff(c_442, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_350])).
% 9.61/3.47  tff(c_896, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_442, c_864])).
% 9.61/3.47  tff(c_921, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_896])).
% 9.61/3.47  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.61/3.47  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.61/3.47  tff(c_661, plain, (![A_73, B_74]: (k4_xboole_0(k2_xboole_0(A_73, B_74), B_74)=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.61/3.47  tff(c_670, plain, (![B_74, A_73]: (k2_xboole_0(B_74, k4_xboole_0(A_73, B_74))=k2_xboole_0(B_74, k2_xboole_0(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_661, c_20])).
% 9.61/3.47  tff(c_705, plain, (![B_74, A_73]: (k2_xboole_0(B_74, k2_xboole_0(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_670])).
% 9.61/3.47  tff(c_1224, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k2_xboole_0(A_87, B_88), C_89)=k2_xboole_0(A_87, k2_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.61/3.47  tff(c_5554, plain, (![A_175, B_176, C_177]: (r1_tarski(k2_xboole_0(A_175, B_176), k2_xboole_0(A_175, k2_xboole_0(B_176, C_177))))), inference(superposition, [status(thm), theory('equality')], [c_1224, c_34])).
% 9.61/3.47  tff(c_6112, plain, (![A_185]: (r1_tarski(k2_xboole_0(A_185, '#skF_5'), k2_xboole_0(A_185, k2_xboole_0('#skF_4', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_43, c_5554])).
% 9.61/3.47  tff(c_6122, plain, (r1_tarski(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_705, c_6112])).
% 9.61/3.47  tff(c_6202, plain, (r1_tarski(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6122])).
% 9.61/3.47  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.61/3.47  tff(c_17074, plain, (![A_274, B_275, C_276]: (k4_xboole_0(k4_xboole_0(A_274, B_275), C_276)=k1_xboole_0 | ~r1_tarski(A_274, k2_xboole_0(B_275, C_276)))), inference(resolution, [status(thm)], [c_1668, c_16])).
% 9.61/3.47  tff(c_17414, plain, (![A_277]: (k4_xboole_0(k4_xboole_0(A_277, '#skF_5'), '#skF_6')=k1_xboole_0 | ~r1_tarski(A_277, k2_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_43, c_17074])).
% 9.61/3.47  tff(c_17458, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6202, c_17414])).
% 9.61/3.47  tff(c_17562, plain, (k4_xboole_0('#skF_3', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_921, c_24, c_17458])).
% 9.61/3.47  tff(c_218, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.61/3.47  tff(c_242, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_218])).
% 9.61/3.47  tff(c_520, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.61/3.47  tff(c_547, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k4_xboole_0(A_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_242, c_520])).
% 9.61/3.47  tff(c_560, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_547])).
% 9.61/3.47  tff(c_2091, plain, (![A_113, B_114]: (k4_xboole_0(k2_xboole_0(A_113, B_114), A_113)=k4_xboole_0(B_114, A_113))), inference(superposition, [status(thm), theory('equality')], [c_2, c_661])).
% 9.61/3.47  tff(c_30, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.61/3.47  tff(c_2110, plain, (![A_113, B_114]: (k4_xboole_0(k2_xboole_0(A_113, B_114), k4_xboole_0(B_114, A_113))=k3_xboole_0(k2_xboole_0(A_113, B_114), A_113))), inference(superposition, [status(thm), theory('equality')], [c_2091, c_30])).
% 9.61/3.47  tff(c_2162, plain, (![A_113, B_114]: (k4_xboole_0(k2_xboole_0(A_113, B_114), k4_xboole_0(B_114, A_113))=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_560, c_4, c_2110])).
% 9.61/3.47  tff(c_17622, plain, (k4_xboole_0(k2_xboole_0('#skF_6', '#skF_3'), k1_xboole_0)='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_17562, c_2162])).
% 9.61/3.47  tff(c_17678, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16263, c_22, c_2, c_17622])).
% 9.61/3.47  tff(c_364, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_349])).
% 9.61/3.47  tff(c_899, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_364, c_864])).
% 9.61/3.47  tff(c_922, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_899])).
% 9.61/3.47  tff(c_17731, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17678, c_922])).
% 9.61/3.47  tff(c_902, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_350, c_864])).
% 9.61/3.47  tff(c_923, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_902])).
% 9.61/3.47  tff(c_689, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_43, c_661])).
% 9.61/3.47  tff(c_17733, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17678, c_17678, c_689])).
% 9.61/3.47  tff(c_17763, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_24, c_17733])).
% 9.61/3.47  tff(c_18526, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17731, c_17763])).
% 9.61/3.47  tff(c_18527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_18526])).
% 9.61/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.47  
% 9.61/3.47  Inference rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Ref     : 0
% 9.61/3.47  #Sup     : 4607
% 9.61/3.47  #Fact    : 0
% 9.61/3.47  #Define  : 0
% 9.61/3.47  #Split   : 4
% 9.61/3.47  #Chain   : 0
% 9.61/3.47  #Close   : 0
% 9.61/3.47  
% 9.61/3.47  Ordering : KBO
% 9.61/3.47  
% 9.61/3.47  Simplification rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Subsume      : 96
% 9.61/3.47  #Demod        : 4721
% 9.61/3.47  #Tautology    : 3089
% 9.61/3.47  #SimpNegUnit  : 21
% 9.61/3.47  #BackRed      : 45
% 9.61/3.47  
% 9.61/3.47  #Partial instantiations: 0
% 9.61/3.47  #Strategies tried      : 1
% 9.61/3.47  
% 9.61/3.47  Timing (in seconds)
% 9.61/3.47  ----------------------
% 9.61/3.47  Preprocessing        : 0.31
% 9.61/3.47  Parsing              : 0.17
% 9.61/3.47  CNF conversion       : 0.02
% 9.61/3.47  Main loop            : 2.38
% 9.61/3.47  Inferencing          : 0.48
% 9.61/3.47  Reduction            : 1.34
% 9.61/3.47  Demodulation         : 1.18
% 9.61/3.47  BG Simplification    : 0.06
% 9.61/3.47  Subsumption          : 0.38
% 9.61/3.47  Abstraction          : 0.07
% 9.61/3.47  MUC search           : 0.00
% 9.61/3.47  Cooper               : 0.00
% 9.61/3.47  Total                : 2.73
% 9.61/3.47  Index Insertion      : 0.00
% 9.61/3.47  Index Deletion       : 0.00
% 9.61/3.47  Index Matching       : 0.00
% 9.61/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
