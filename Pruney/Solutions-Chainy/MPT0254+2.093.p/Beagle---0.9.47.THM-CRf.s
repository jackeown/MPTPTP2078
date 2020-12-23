%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:31 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 863 expanded)
%              Number of leaves         :   40 ( 306 expanded)
%              Depth                    :   16
%              Number of atoms          :   76 ( 847 expanded)
%              Number of equality atoms :   58 ( 829 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_204,plain,(
    ! [B_78,A_79] : k5_xboole_0(B_78,A_79) = k5_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_220,plain,(
    ! [A_79] : k5_xboole_0(k1_xboole_0,A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_20])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_723,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k5_xboole_0(A_122,B_123),C_124) = k5_xboole_0(A_122,k5_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_804,plain,(
    ! [A_23,C_124] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_124)) = k5_xboole_0(k1_xboole_0,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_723])).

tff(c_824,plain,(
    ! [A_23,C_124] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_124)) = C_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_804])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_868,plain,(
    ! [A_127,C_128] : k5_xboole_0(A_127,k5_xboole_0(A_127,C_128)) = C_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_804])).

tff(c_974,plain,(
    ! [A_132,B_133] : k5_xboole_0(A_132,k5_xboole_0(B_133,A_132)) = B_133 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_868])).

tff(c_1010,plain,(
    ! [A_23,C_124] : k5_xboole_0(k5_xboole_0(A_23,C_124),C_124) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_974])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_377,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_400,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_377])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_736,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k5_xboole_0(B_123,k3_xboole_0(A_122,B_123))) = k2_xboole_0(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_28])).

tff(c_1334,plain,(
    ! [A_148,B_149] : k5_xboole_0(A_148,k4_xboole_0(B_149,A_148)) = k2_xboole_0(A_148,B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_736])).

tff(c_1565,plain,(
    ! [A_165,B_166] : k5_xboole_0(A_165,k2_xboole_0(A_165,B_166)) = k4_xboole_0(B_166,A_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_824])).

tff(c_1617,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1565])).

tff(c_1626,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1617])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1639,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_18])).

tff(c_1644,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_1639])).

tff(c_1652,plain,(
    k5_xboole_0(k5_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) = k2_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_28])).

tff(c_1667,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_1652])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_910,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_868])).

tff(c_1633,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_4')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_910])).

tff(c_1671,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1644,c_1633])).

tff(c_1690,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k3_xboole_0('#skF_5',k1_tarski('#skF_4'))) = k2_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1671,c_28])).

tff(c_1694,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1644,c_1690])).

tff(c_1724,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_1694])).

tff(c_22,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_359,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,k3_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_371,plain,(
    ! [A_14,C_95] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_95,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_359])).

tff(c_373,plain,(
    ! [C_95] : ~ r2_hidden(C_95,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_371])).

tff(c_1732,plain,(
    ! [C_95] : ~ r2_hidden(C_95,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_373])).

tff(c_623,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k3_xboole_0(A_118,B_119)) = k2_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_677,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_623])).

tff(c_691,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_677])).

tff(c_1856,plain,(
    ! [A_179] : k2_xboole_0(A_179,'#skF_5') = A_179 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_691])).

tff(c_1735,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_70])).

tff(c_1862,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1856,c_1735])).

tff(c_54,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_337,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [E_32,B_27,C_28] : r2_hidden(E_32,k1_enumset1(E_32,B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_355,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_36])).

tff(c_358,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_355])).

tff(c_1899,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_358])).

tff(c_1903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_1899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:08:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.50/1.57  
% 3.50/1.57  %Foreground sorts:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Background operators:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Foreground operators:
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.50/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.50/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.50/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.50/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.50/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.50/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.50/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.57  
% 3.50/1.58  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.50/1.58  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.50/1.58  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.50/1.58  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.50/1.58  tff(f_100, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.50/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.50/1.58  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.50/1.58  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.50/1.58  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.50/1.58  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.50/1.58  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.50/1.58  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.50/1.58  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.50/1.58  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.50/1.58  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.50/1.58  tff(c_204, plain, (![B_78, A_79]: (k5_xboole_0(B_78, A_79)=k5_xboole_0(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.58  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.50/1.58  tff(c_220, plain, (![A_79]: (k5_xboole_0(k1_xboole_0, A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_204, c_20])).
% 3.50/1.58  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.50/1.58  tff(c_723, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k5_xboole_0(A_122, B_123), C_124)=k5_xboole_0(A_122, k5_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.50/1.58  tff(c_804, plain, (![A_23, C_124]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_124))=k5_xboole_0(k1_xboole_0, C_124))), inference(superposition, [status(thm), theory('equality')], [c_26, c_723])).
% 3.50/1.58  tff(c_824, plain, (![A_23, C_124]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_124))=C_124)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_804])).
% 3.50/1.58  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.58  tff(c_868, plain, (![A_127, C_128]: (k5_xboole_0(A_127, k5_xboole_0(A_127, C_128))=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_804])).
% 3.50/1.58  tff(c_974, plain, (![A_132, B_133]: (k5_xboole_0(A_132, k5_xboole_0(B_133, A_132))=B_133)), inference(superposition, [status(thm), theory('equality')], [c_4, c_868])).
% 3.50/1.58  tff(c_1010, plain, (![A_23, C_124]: (k5_xboole_0(k5_xboole_0(A_23, C_124), C_124)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_824, c_974])).
% 3.50/1.58  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.50/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.50/1.58  tff(c_377, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.58  tff(c_400, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_377])).
% 3.50/1.58  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.50/1.58  tff(c_736, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, k3_xboole_0(A_122, B_123)))=k2_xboole_0(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_723, c_28])).
% 3.50/1.58  tff(c_1334, plain, (![A_148, B_149]: (k5_xboole_0(A_148, k4_xboole_0(B_149, A_148))=k2_xboole_0(A_148, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_736])).
% 3.50/1.58  tff(c_1565, plain, (![A_165, B_166]: (k5_xboole_0(A_165, k2_xboole_0(A_165, B_166))=k4_xboole_0(B_166, A_165))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_824])).
% 3.50/1.58  tff(c_1617, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1565])).
% 3.50/1.58  tff(c_1626, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1617])).
% 3.50/1.58  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.50/1.58  tff(c_1639, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1626, c_18])).
% 3.50/1.58  tff(c_1644, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_1639])).
% 3.50/1.58  tff(c_1652, plain, (k5_xboole_0(k5_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))=k2_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1644, c_28])).
% 3.50/1.58  tff(c_1667, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_1652])).
% 3.50/1.58  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.58  tff(c_910, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(superposition, [status(thm), theory('equality')], [c_10, c_868])).
% 3.50/1.58  tff(c_1633, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_4'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1626, c_910])).
% 3.50/1.58  tff(c_1671, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1644, c_1633])).
% 3.50/1.58  tff(c_1690, plain, (k5_xboole_0(k1_tarski('#skF_4'), k3_xboole_0('#skF_5', k1_tarski('#skF_4')))=k2_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1671, c_28])).
% 3.50/1.58  tff(c_1694, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1644, c_1690])).
% 3.50/1.58  tff(c_1724, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_1694])).
% 3.50/1.58  tff(c_22, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.50/1.58  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.50/1.58  tff(c_359, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, k3_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.50/1.58  tff(c_371, plain, (![A_14, C_95]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_359])).
% 3.50/1.58  tff(c_373, plain, (![C_95]: (~r2_hidden(C_95, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_371])).
% 3.50/1.58  tff(c_1732, plain, (![C_95]: (~r2_hidden(C_95, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1724, c_373])).
% 3.50/1.58  tff(c_623, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k3_xboole_0(A_118, B_119))=k2_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.50/1.58  tff(c_677, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_623])).
% 3.50/1.58  tff(c_691, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_677])).
% 3.50/1.58  tff(c_1856, plain, (![A_179]: (k2_xboole_0(A_179, '#skF_5')=A_179)), inference(demodulation, [status(thm), theory('equality')], [c_1724, c_691])).
% 3.50/1.58  tff(c_1735, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1724, c_70])).
% 3.50/1.58  tff(c_1862, plain, (k1_tarski('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1856, c_1735])).
% 3.50/1.58  tff(c_54, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.50/1.58  tff(c_337, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.50/1.58  tff(c_36, plain, (![E_32, B_27, C_28]: (r2_hidden(E_32, k1_enumset1(E_32, B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.50/1.58  tff(c_355, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_36])).
% 3.50/1.58  tff(c_358, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_355])).
% 3.50/1.58  tff(c_1899, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1862, c_358])).
% 3.50/1.58  tff(c_1903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1732, c_1899])).
% 3.50/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.58  
% 3.50/1.58  Inference rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Ref     : 0
% 3.50/1.58  #Sup     : 452
% 3.50/1.58  #Fact    : 0
% 3.50/1.58  #Define  : 0
% 3.50/1.58  #Split   : 0
% 3.50/1.58  #Chain   : 0
% 3.50/1.58  #Close   : 0
% 3.50/1.58  
% 3.50/1.58  Ordering : KBO
% 3.50/1.58  
% 3.50/1.58  Simplification rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Subsume      : 17
% 3.50/1.58  #Demod        : 262
% 3.50/1.58  #Tautology    : 289
% 3.50/1.58  #SimpNegUnit  : 3
% 3.50/1.58  #BackRed      : 22
% 3.50/1.58  
% 3.50/1.58  #Partial instantiations: 0
% 3.50/1.58  #Strategies tried      : 1
% 3.50/1.58  
% 3.50/1.58  Timing (in seconds)
% 3.50/1.58  ----------------------
% 3.50/1.59  Preprocessing        : 0.34
% 3.50/1.59  Parsing              : 0.18
% 3.50/1.59  CNF conversion       : 0.02
% 3.50/1.59  Main loop            : 0.48
% 3.50/1.59  Inferencing          : 0.16
% 3.50/1.59  Reduction            : 0.20
% 3.50/1.59  Demodulation         : 0.16
% 3.50/1.59  BG Simplification    : 0.03
% 3.50/1.59  Subsumption          : 0.07
% 3.50/1.59  Abstraction          : 0.03
% 3.50/1.59  MUC search           : 0.00
% 3.50/1.59  Cooper               : 0.00
% 3.50/1.59  Total                : 0.86
% 3.50/1.59  Index Insertion      : 0.00
% 3.50/1.59  Index Deletion       : 0.00
% 3.50/1.59  Index Matching       : 0.00
% 3.50/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
