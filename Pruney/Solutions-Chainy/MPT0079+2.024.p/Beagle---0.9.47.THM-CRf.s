%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 11.13s
% Output     : CNFRefutation 11.23s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 775 expanded)
%              Number of leaves         :   32 ( 280 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 986 expanded)
%              Number of equality atoms :   69 ( 683 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_108,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(A_44,B_45)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_108])).

tff(c_367,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_393,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = k3_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_367])).

tff(c_691,plain,(
    ! [A_70,B_71] : k2_xboole_0(k3_xboole_0(A_70,B_71),k4_xboole_0(A_70,B_71)) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_724,plain,(
    ! [A_17] : k2_xboole_0(k4_xboole_0(A_17,k1_xboole_0),k4_xboole_0(A_17,A_17)) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_691])).

tff(c_764,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_118,c_724])).

tff(c_42,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1244,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_92)
      | r1_xboole_0(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4656,plain,(
    ! [A_193,B_194,A_195] :
      ( ~ r1_xboole_0(A_193,B_194)
      | r1_xboole_0(A_195,k3_xboole_0(A_193,B_194)) ) ),
    inference(resolution,[status(thm)],[c_1244,c_14])).

tff(c_36,plain,(
    ! [A_34] :
      ( ~ r1_xboole_0(A_34,A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4718,plain,(
    ! [A_198,B_199] :
      ( k3_xboole_0(A_198,B_199) = k1_xboole_0
      | ~ r1_xboole_0(A_198,B_199) ) ),
    inference(resolution,[status(thm)],[c_4656,c_36])).

tff(c_4747,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_4718])).

tff(c_32,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4811,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4747,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_464,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_485,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_464])).

tff(c_5150,plain,(
    k4_xboole_0(k4_xboole_0('#skF_6','#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4811,c_485])).

tff(c_5197,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_764,c_5150])).

tff(c_128,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_47,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_152,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_47])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1519,plain,(
    ! [A_99,B_100] : k2_xboole_0(A_99,k4_xboole_0(B_100,A_99)) = k2_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1574,plain,(
    ! [B_21,A_20] : k2_xboole_0(B_21,k4_xboole_0(A_20,B_21)) = k2_xboole_0(B_21,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1519])).

tff(c_5966,plain,(
    ! [B_206,A_207] : k2_xboole_0(B_206,k2_xboole_0(A_207,B_206)) = k2_xboole_0(B_206,A_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1574])).

tff(c_6120,plain,(
    k2_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_5966])).

tff(c_6161,plain,(
    k2_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_6120])).

tff(c_2183,plain,(
    ! [A_122,B_123,C_124] : k2_xboole_0(k2_xboole_0(A_122,B_123),C_124) = k2_xboole_0(A_122,k2_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7323,plain,(
    ! [A_229,B_230,C_231] : r1_tarski(k2_xboole_0(A_229,B_230),k2_xboole_0(A_229,k2_xboole_0(B_230,C_231))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2183,c_38])).

tff(c_7335,plain,(
    r1_tarski(k2_xboole_0('#skF_6','#skF_4'),k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6161,c_7323])).

tff(c_7500,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_6'),k2_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7335])).

tff(c_2742,plain,(
    ! [A_136,B_137,C_138] :
      ( r1_tarski(k4_xboole_0(A_136,B_137),C_138)
      | ~ r1_tarski(A_136,k2_xboole_0(B_137,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_23772,plain,(
    ! [A_336,B_337,C_338] :
      ( k2_xboole_0(k4_xboole_0(A_336,B_337),C_338) = C_338
      | ~ r1_tarski(A_336,k2_xboole_0(B_337,C_338)) ) ),
    inference(resolution,[status(thm)],[c_2742,c_16])).

tff(c_23865,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7500,c_23772])).

tff(c_24099,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5197,c_2,c_485,c_23865])).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4748,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_4718])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5267,plain,(
    ! [A_200,B_201] : k2_xboole_0(k3_xboole_0(A_200,B_201),k4_xboole_0(B_201,A_200)) = B_201 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_691])).

tff(c_5337,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4748,c_5267])).

tff(c_5599,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_5'),k1_xboole_0) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5337,c_485])).

tff(c_5646,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_764,c_5599])).

tff(c_1605,plain,(
    ! [B_21,A_20] : k2_xboole_0(B_21,k2_xboole_0(A_20,B_21)) = k2_xboole_0(B_21,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1574])).

tff(c_8175,plain,(
    ! [A_241] : r1_tarski(k2_xboole_0(A_241,'#skF_5'),k2_xboole_0(A_241,k2_xboole_0('#skF_4','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_7323])).

tff(c_8205,plain,(
    r1_tarski(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1605,c_8175])).

tff(c_8279,plain,(
    r1_tarski(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8205])).

tff(c_25022,plain,(
    ! [A_339,B_340,C_341] :
      ( r1_tarski(k4_xboole_0(A_339,B_340),C_341)
      | ~ r1_tarski(k2_xboole_0(A_339,B_340),k2_xboole_0(B_340,C_341)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2742])).

tff(c_25636,plain,(
    ! [A_343] :
      ( r1_tarski(k4_xboole_0(A_343,'#skF_5'),'#skF_6')
      | ~ r1_tarski(k2_xboole_0(A_343,'#skF_5'),k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_25022])).

tff(c_25658,plain,(
    r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_8279,c_25636])).

tff(c_25711,plain,(
    r1_tarski('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5646,c_25658])).

tff(c_25729,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_25711,c_16])).

tff(c_25731,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24099,c_25729])).

tff(c_5340,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4747,c_5267])).

tff(c_5730,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_6'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5340,c_485])).

tff(c_5777,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_764,c_5730])).

tff(c_25760,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25731,c_5777])).

tff(c_4913,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4748,c_32])).

tff(c_5467,plain,(
    k4_xboole_0(k4_xboole_0('#skF_5','#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4913,c_485])).

tff(c_5514,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_764,c_5467])).

tff(c_491,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_464])).

tff(c_25776,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25731,c_25731,c_491])).

tff(c_25811,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5514,c_22,c_25776])).

tff(c_26462,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25760,c_25811])).

tff(c_26463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.13/4.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.23/4.68  
% 11.23/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.23/4.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.23/4.68  
% 11.23/4.68  %Foreground sorts:
% 11.23/4.68  
% 11.23/4.68  
% 11.23/4.68  %Background operators:
% 11.23/4.68  
% 11.23/4.68  
% 11.23/4.68  %Foreground operators:
% 11.23/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.23/4.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.23/4.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.23/4.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.23/4.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.23/4.68  tff('#skF_5', type, '#skF_5': $i).
% 11.23/4.68  tff('#skF_6', type, '#skF_6': $i).
% 11.23/4.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.23/4.68  tff('#skF_3', type, '#skF_3': $i).
% 11.23/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.23/4.68  tff('#skF_4', type, '#skF_4': $i).
% 11.23/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.23/4.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.23/4.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.23/4.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.23/4.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.23/4.68  
% 11.23/4.70  tff(f_106, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 11.23/4.70  tff(f_67, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.23/4.70  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.23/4.70  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.23/4.70  tff(f_83, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.23/4.70  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.23/4.70  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.23/4.70  tff(f_95, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 11.23/4.70  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.23/4.70  tff(f_71, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 11.23/4.70  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.23/4.70  tff(f_81, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.23/4.70  tff(f_97, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.23/4.70  tff(f_75, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.23/4.70  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.23/4.70  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.23/4.70  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.23/4.70  tff(c_18, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.23/4.70  tff(c_108, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(A_44, B_45))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.23/4.70  tff(c_118, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_108])).
% 11.23/4.70  tff(c_367, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.23/4.70  tff(c_393, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=k3_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_118, c_367])).
% 11.23/4.70  tff(c_691, plain, (![A_70, B_71]: (k2_xboole_0(k3_xboole_0(A_70, B_71), k4_xboole_0(A_70, B_71))=A_70)), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.23/4.70  tff(c_724, plain, (![A_17]: (k2_xboole_0(k4_xboole_0(A_17, k1_xboole_0), k4_xboole_0(A_17, A_17))=A_17)), inference(superposition, [status(thm), theory('equality')], [c_393, c_691])).
% 11.23/4.70  tff(c_764, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_118, c_724])).
% 11.23/4.70  tff(c_42, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.23/4.70  tff(c_1244, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), B_92) | r1_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.23/4.70  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.23/4.70  tff(c_4656, plain, (![A_193, B_194, A_195]: (~r1_xboole_0(A_193, B_194) | r1_xboole_0(A_195, k3_xboole_0(A_193, B_194)))), inference(resolution, [status(thm)], [c_1244, c_14])).
% 11.23/4.70  tff(c_36, plain, (![A_34]: (~r1_xboole_0(A_34, A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.23/4.70  tff(c_4718, plain, (![A_198, B_199]: (k3_xboole_0(A_198, B_199)=k1_xboole_0 | ~r1_xboole_0(A_198, B_199))), inference(resolution, [status(thm)], [c_4656, c_36])).
% 11.23/4.70  tff(c_4747, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_4718])).
% 11.23/4.70  tff(c_32, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.23/4.70  tff(c_4811, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4747, c_32])).
% 11.23/4.70  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.23/4.70  tff(c_464, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.23/4.70  tff(c_485, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_464])).
% 11.23/4.70  tff(c_5150, plain, (k4_xboole_0(k4_xboole_0('#skF_6', '#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4811, c_485])).
% 11.23/4.70  tff(c_5197, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_764, c_764, c_5150])).
% 11.23/4.70  tff(c_128, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.23/4.70  tff(c_46, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.23/4.70  tff(c_47, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 11.23/4.70  tff(c_152, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128, c_47])).
% 11.23/4.70  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.23/4.70  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.23/4.70  tff(c_1519, plain, (![A_99, B_100]: (k2_xboole_0(A_99, k4_xboole_0(B_100, A_99))=k2_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.23/4.70  tff(c_1574, plain, (![B_21, A_20]: (k2_xboole_0(B_21, k4_xboole_0(A_20, B_21))=k2_xboole_0(B_21, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1519])).
% 11.23/4.70  tff(c_5966, plain, (![B_206, A_207]: (k2_xboole_0(B_206, k2_xboole_0(A_207, B_206))=k2_xboole_0(B_206, A_207))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1574])).
% 11.23/4.70  tff(c_6120, plain, (k2_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_47, c_5966])).
% 11.23/4.70  tff(c_6161, plain, (k2_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_6120])).
% 11.23/4.70  tff(c_2183, plain, (![A_122, B_123, C_124]: (k2_xboole_0(k2_xboole_0(A_122, B_123), C_124)=k2_xboole_0(A_122, k2_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.23/4.70  tff(c_38, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.23/4.70  tff(c_7323, plain, (![A_229, B_230, C_231]: (r1_tarski(k2_xboole_0(A_229, B_230), k2_xboole_0(A_229, k2_xboole_0(B_230, C_231))))), inference(superposition, [status(thm), theory('equality')], [c_2183, c_38])).
% 11.23/4.70  tff(c_7335, plain, (r1_tarski(k2_xboole_0('#skF_6', '#skF_4'), k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6161, c_7323])).
% 11.23/4.70  tff(c_7500, plain, (r1_tarski(k2_xboole_0('#skF_4', '#skF_6'), k2_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7335])).
% 11.23/4.70  tff(c_2742, plain, (![A_136, B_137, C_138]: (r1_tarski(k4_xboole_0(A_136, B_137), C_138) | ~r1_tarski(A_136, k2_xboole_0(B_137, C_138)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.23/4.70  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.23/4.70  tff(c_23772, plain, (![A_336, B_337, C_338]: (k2_xboole_0(k4_xboole_0(A_336, B_337), C_338)=C_338 | ~r1_tarski(A_336, k2_xboole_0(B_337, C_338)))), inference(resolution, [status(thm)], [c_2742, c_16])).
% 11.23/4.70  tff(c_23865, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_7500, c_23772])).
% 11.23/4.70  tff(c_24099, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5197, c_2, c_485, c_23865])).
% 11.23/4.70  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.23/4.70  tff(c_4748, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_4718])).
% 11.23/4.70  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.23/4.70  tff(c_5267, plain, (![A_200, B_201]: (k2_xboole_0(k3_xboole_0(A_200, B_201), k4_xboole_0(B_201, A_200))=B_201)), inference(superposition, [status(thm), theory('equality')], [c_4, c_691])).
% 11.23/4.70  tff(c_5337, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4748, c_5267])).
% 11.23/4.70  tff(c_5599, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), k1_xboole_0)=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5337, c_485])).
% 11.23/4.70  tff(c_5646, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_764, c_764, c_5599])).
% 11.23/4.70  tff(c_1605, plain, (![B_21, A_20]: (k2_xboole_0(B_21, k2_xboole_0(A_20, B_21))=k2_xboole_0(B_21, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1574])).
% 11.23/4.70  tff(c_8175, plain, (![A_241]: (r1_tarski(k2_xboole_0(A_241, '#skF_5'), k2_xboole_0(A_241, k2_xboole_0('#skF_4', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_47, c_7323])).
% 11.23/4.70  tff(c_8205, plain, (r1_tarski(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1605, c_8175])).
% 11.23/4.70  tff(c_8279, plain, (r1_tarski(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8205])).
% 11.23/4.70  tff(c_25022, plain, (![A_339, B_340, C_341]: (r1_tarski(k4_xboole_0(A_339, B_340), C_341) | ~r1_tarski(k2_xboole_0(A_339, B_340), k2_xboole_0(B_340, C_341)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2742])).
% 11.23/4.70  tff(c_25636, plain, (![A_343]: (r1_tarski(k4_xboole_0(A_343, '#skF_5'), '#skF_6') | ~r1_tarski(k2_xboole_0(A_343, '#skF_5'), k2_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_47, c_25022])).
% 11.23/4.70  tff(c_25658, plain, (r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_8279, c_25636])).
% 11.23/4.70  tff(c_25711, plain, (r1_tarski('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5646, c_25658])).
% 11.23/4.70  tff(c_25729, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_25711, c_16])).
% 11.23/4.70  tff(c_25731, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24099, c_25729])).
% 11.23/4.70  tff(c_5340, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4747, c_5267])).
% 11.23/4.70  tff(c_5730, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5340, c_485])).
% 11.23/4.70  tff(c_5777, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_764, c_764, c_5730])).
% 11.23/4.70  tff(c_25760, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25731, c_5777])).
% 11.23/4.70  tff(c_4913, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4748, c_32])).
% 11.23/4.70  tff(c_5467, plain, (k4_xboole_0(k4_xboole_0('#skF_5', '#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4913, c_485])).
% 11.23/4.70  tff(c_5514, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_764, c_764, c_5467])).
% 11.23/4.70  tff(c_491, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_47, c_464])).
% 11.23/4.70  tff(c_25776, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25731, c_25731, c_491])).
% 11.23/4.70  tff(c_25811, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5514, c_22, c_25776])).
% 11.23/4.70  tff(c_26462, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25760, c_25811])).
% 11.23/4.70  tff(c_26463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26462])).
% 11.23/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.23/4.70  
% 11.23/4.70  Inference rules
% 11.23/4.70  ----------------------
% 11.23/4.70  #Ref     : 0
% 11.23/4.70  #Sup     : 6625
% 11.23/4.70  #Fact    : 0
% 11.23/4.70  #Define  : 0
% 11.23/4.70  #Split   : 0
% 11.23/4.70  #Chain   : 0
% 11.23/4.70  #Close   : 0
% 11.23/4.70  
% 11.23/4.70  Ordering : KBO
% 11.23/4.70  
% 11.23/4.70  Simplification rules
% 11.23/4.70  ----------------------
% 11.23/4.70  #Subsume      : 150
% 11.23/4.70  #Demod        : 7282
% 11.23/4.70  #Tautology    : 4392
% 11.23/4.70  #SimpNegUnit  : 19
% 11.23/4.70  #BackRed      : 60
% 11.23/4.70  
% 11.23/4.70  #Partial instantiations: 0
% 11.23/4.70  #Strategies tried      : 1
% 11.23/4.70  
% 11.23/4.70  Timing (in seconds)
% 11.23/4.70  ----------------------
% 11.23/4.70  Preprocessing        : 0.31
% 11.23/4.70  Parsing              : 0.16
% 11.23/4.70  CNF conversion       : 0.02
% 11.23/4.70  Main loop            : 3.54
% 11.23/4.70  Inferencing          : 0.57
% 11.23/4.70  Reduction            : 2.17
% 11.23/4.70  Demodulation         : 1.95
% 11.23/4.70  BG Simplification    : 0.07
% 11.23/4.70  Subsumption          : 0.58
% 11.23/4.70  Abstraction          : 0.11
% 11.23/4.70  MUC search           : 0.00
% 11.23/4.70  Cooper               : 0.00
% 11.23/4.70  Total                : 3.88
% 11.23/4.70  Index Insertion      : 0.00
% 11.23/4.70  Index Deletion       : 0.00
% 11.23/4.71  Index Matching       : 0.00
% 11.23/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
