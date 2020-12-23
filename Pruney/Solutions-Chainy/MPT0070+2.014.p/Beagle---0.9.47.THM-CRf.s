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
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 205 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 265 expanded)
%              Number of equality atoms :   49 ( 139 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_507,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4546,plain,(
    ! [A_146,B_147] :
      ( ~ r1_xboole_0(A_146,B_147)
      | k3_xboole_0(A_146,B_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_507])).

tff(c_4550,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_4546])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4557,plain,(
    ! [C_9] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4550,c_8])).

tff(c_4565,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4557])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_529,plain,(
    ! [A_14,C_52] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_507])).

tff(c_538,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_200,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_221,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_200])).

tff(c_226,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_221])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1087,plain,(
    ! [A_72,B_73] :
      ( ~ r1_xboole_0(A_72,B_73)
      | k3_xboole_0(A_72,B_73) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_507])).

tff(c_1101,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1087])).

tff(c_351,plain,(
    ! [A_45,B_46] : k2_xboole_0(k3_xboole_0(A_45,B_46),k4_xboole_0(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1489,plain,(
    ! [B_81,A_82] : k2_xboole_0(k3_xboole_0(B_81,A_82),k4_xboole_0(A_82,B_81)) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_351])).

tff(c_1526,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_1489])).

tff(c_384,plain,(
    ! [A_17] : k2_xboole_0(k3_xboole_0(A_17,k1_xboole_0),A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_351])).

tff(c_393,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_384])).

tff(c_1619,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_393])).

tff(c_227,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_221])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_232,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k3_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_24])).

tff(c_247,plain,(
    ! [A_41] : k3_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_232])).

tff(c_366,plain,(
    ! [A_17] : k2_xboole_0(k3_xboole_0(A_17,A_17),k1_xboole_0) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_351])).

tff(c_391,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_366])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_235,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = k2_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_18])).

tff(c_430,plain,(
    ! [A_41] : k2_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_235])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_175,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_167])).

tff(c_180,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_180])).

tff(c_284,plain,(
    k2_xboole_0('#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_189])).

tff(c_475,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_284])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3520,plain,(
    ! [C_117] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_4',C_117)) = k4_xboole_0('#skF_5',C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_22])).

tff(c_3581,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_3520])).

tff(c_3619,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_3581])).

tff(c_3652,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3619,c_24])).

tff(c_3666,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_4,c_3652])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3707,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_5'),k1_xboole_0)
    | r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3666,c_6])).

tff(c_3728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_538,c_3707])).

tff(c_3729,plain,(
    ! [A_14] : ~ r1_xboole_0(A_14,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_82,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_30] : k3_xboole_0(k1_xboole_0,A_30) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_520,plain,(
    ! [A_30,C_52] :
      ( ~ r1_xboole_0(k1_xboole_0,A_30)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_507])).

tff(c_3893,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_4062,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_1'(A_128,B_129),k3_xboole_0(A_128,B_129))
      | r1_xboole_0(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4083,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4062])).

tff(c_4088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3729,c_3893,c_4083])).

tff(c_4089,plain,(
    ! [A_30] : ~ r1_xboole_0(k1_xboole_0,A_30) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_4373,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_1'(A_138,B_139),k3_xboole_0(A_138,B_139))
      | r1_xboole_0(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4391,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(k1_xboole_0,A_30),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4373])).

tff(c_4403,plain,(
    ! [A_30] : r2_hidden('#skF_1'(k1_xboole_0,A_30),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_4089,c_4391])).

tff(c_4569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4565,c_4403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:12:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.94  
% 4.56/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 4.56/1.94  
% 4.56/1.94  %Foreground sorts:
% 4.56/1.94  
% 4.56/1.94  
% 4.56/1.94  %Background operators:
% 4.56/1.94  
% 4.56/1.94  
% 4.56/1.94  %Foreground operators:
% 4.56/1.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.56/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.56/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.56/1.94  
% 4.56/1.96  tff(f_74, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.56/1.96  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.56/1.96  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.56/1.96  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.56/1.96  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.56/1.96  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.56/1.96  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.56/1.96  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.56/1.96  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.56/1.96  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.56/1.96  tff(f_63, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.56/1.96  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.56/1.96  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.56/1.96  tff(c_507, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.96  tff(c_4546, plain, (![A_146, B_147]: (~r1_xboole_0(A_146, B_147) | k3_xboole_0(A_146, B_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_507])).
% 4.56/1.96  tff(c_4550, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_4546])).
% 4.56/1.96  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.96  tff(c_4557, plain, (![C_9]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4550, c_8])).
% 4.56/1.96  tff(c_4565, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4557])).
% 4.56/1.96  tff(c_28, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.56/1.96  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.56/1.96  tff(c_529, plain, (![A_14, C_52]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_507])).
% 4.56/1.96  tff(c_538, plain, (![C_52]: (~r2_hidden(C_52, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_529])).
% 4.56/1.96  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.56/1.96  tff(c_200, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.56/1.96  tff(c_221, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_200])).
% 4.56/1.96  tff(c_226, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_221])).
% 4.56/1.96  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/1.96  tff(c_1087, plain, (![A_72, B_73]: (~r1_xboole_0(A_72, B_73) | k3_xboole_0(A_72, B_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_507])).
% 4.56/1.96  tff(c_1101, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_1087])).
% 4.56/1.96  tff(c_351, plain, (![A_45, B_46]: (k2_xboole_0(k3_xboole_0(A_45, B_46), k4_xboole_0(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.56/1.96  tff(c_1489, plain, (![B_81, A_82]: (k2_xboole_0(k3_xboole_0(B_81, A_82), k4_xboole_0(A_82, B_81))=A_82)), inference(superposition, [status(thm), theory('equality')], [c_4, c_351])).
% 4.56/1.96  tff(c_1526, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1101, c_1489])).
% 4.56/1.96  tff(c_384, plain, (![A_17]: (k2_xboole_0(k3_xboole_0(A_17, k1_xboole_0), A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_20, c_351])).
% 4.56/1.96  tff(c_393, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_384])).
% 4.56/1.96  tff(c_1619, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1526, c_393])).
% 4.56/1.96  tff(c_227, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_221])).
% 4.56/1.96  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.56/1.96  tff(c_232, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k3_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_227, c_24])).
% 4.56/1.96  tff(c_247, plain, (![A_41]: (k3_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_232])).
% 4.56/1.96  tff(c_366, plain, (![A_17]: (k2_xboole_0(k3_xboole_0(A_17, A_17), k1_xboole_0)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_226, c_351])).
% 4.56/1.96  tff(c_391, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_366])).
% 4.56/1.96  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.96  tff(c_235, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=k2_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_227, c_18])).
% 4.56/1.96  tff(c_430, plain, (![A_41]: (k2_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_235])).
% 4.56/1.96  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.56/1.96  tff(c_167, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.56/1.96  tff(c_175, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_167])).
% 4.56/1.96  tff(c_180, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.96  tff(c_189, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_180])).
% 4.56/1.96  tff(c_284, plain, (k2_xboole_0('#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_189])).
% 4.56/1.96  tff(c_475, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_430, c_284])).
% 4.56/1.96  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.56/1.96  tff(c_3520, plain, (![C_117]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', C_117))=k4_xboole_0('#skF_5', C_117))), inference(superposition, [status(thm), theory('equality')], [c_1619, c_22])).
% 4.56/1.96  tff(c_3581, plain, (k4_xboole_0('#skF_5', '#skF_3')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_475, c_3520])).
% 4.56/1.96  tff(c_3619, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1619, c_3581])).
% 4.56/1.96  tff(c_3652, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3619, c_24])).
% 4.56/1.96  tff(c_3666, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_226, c_4, c_3652])).
% 4.56/1.96  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.96  tff(c_3707, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_5'), k1_xboole_0) | r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3666, c_6])).
% 4.56/1.96  tff(c_3728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_538, c_3707])).
% 4.56/1.96  tff(c_3729, plain, (![A_14]: (~r1_xboole_0(A_14, k1_xboole_0))), inference(splitRight, [status(thm)], [c_529])).
% 4.56/1.96  tff(c_82, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/1.96  tff(c_98, plain, (![A_30]: (k3_xboole_0(k1_xboole_0, A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_16])).
% 4.56/1.96  tff(c_520, plain, (![A_30, C_52]: (~r1_xboole_0(k1_xboole_0, A_30) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_98, c_507])).
% 4.56/1.96  tff(c_3893, plain, (![C_52]: (~r2_hidden(C_52, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_520])).
% 4.56/1.96  tff(c_4062, plain, (![A_128, B_129]: (r2_hidden('#skF_1'(A_128, B_129), k3_xboole_0(A_128, B_129)) | r1_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.96  tff(c_4083, plain, (![A_14]: (r2_hidden('#skF_1'(A_14, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4062])).
% 4.56/1.96  tff(c_4088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3729, c_3893, c_4083])).
% 4.56/1.96  tff(c_4089, plain, (![A_30]: (~r1_xboole_0(k1_xboole_0, A_30))), inference(splitRight, [status(thm)], [c_520])).
% 4.56/1.96  tff(c_4373, plain, (![A_138, B_139]: (r2_hidden('#skF_1'(A_138, B_139), k3_xboole_0(A_138, B_139)) | r1_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.96  tff(c_4391, plain, (![A_30]: (r2_hidden('#skF_1'(k1_xboole_0, A_30), k1_xboole_0) | r1_xboole_0(k1_xboole_0, A_30))), inference(superposition, [status(thm), theory('equality')], [c_98, c_4373])).
% 4.56/1.96  tff(c_4403, plain, (![A_30]: (r2_hidden('#skF_1'(k1_xboole_0, A_30), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_4089, c_4391])).
% 4.56/1.96  tff(c_4569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4565, c_4403])).
% 4.56/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.96  
% 4.56/1.96  Inference rules
% 4.56/1.96  ----------------------
% 4.56/1.96  #Ref     : 0
% 4.56/1.96  #Sup     : 1149
% 4.56/1.96  #Fact    : 0
% 4.56/1.96  #Define  : 0
% 4.56/1.96  #Split   : 4
% 4.56/1.96  #Chain   : 0
% 4.56/1.96  #Close   : 0
% 4.56/1.96  
% 4.56/1.96  Ordering : KBO
% 4.56/1.96  
% 4.56/1.96  Simplification rules
% 4.56/1.96  ----------------------
% 4.56/1.96  #Subsume      : 38
% 4.56/1.96  #Demod        : 925
% 4.56/1.96  #Tautology    : 810
% 4.56/1.96  #SimpNegUnit  : 27
% 4.56/1.96  #BackRed      : 11
% 4.56/1.96  
% 4.56/1.96  #Partial instantiations: 0
% 4.56/1.96  #Strategies tried      : 1
% 4.56/1.96  
% 4.56/1.96  Timing (in seconds)
% 4.56/1.96  ----------------------
% 4.56/1.96  Preprocessing        : 0.29
% 4.56/1.96  Parsing              : 0.16
% 4.56/1.96  CNF conversion       : 0.02
% 4.56/1.96  Main loop            : 0.89
% 4.56/1.96  Inferencing          : 0.28
% 4.56/1.96  Reduction            : 0.41
% 4.56/1.96  Demodulation         : 0.33
% 4.56/1.96  BG Simplification    : 0.03
% 4.56/1.96  Subsumption          : 0.12
% 4.56/1.96  Abstraction          : 0.04
% 4.56/1.96  MUC search           : 0.00
% 4.56/1.96  Cooper               : 0.00
% 4.56/1.96  Total                : 1.22
% 4.56/1.96  Index Insertion      : 0.00
% 4.56/1.96  Index Deletion       : 0.00
% 4.56/1.96  Index Matching       : 0.00
% 4.56/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
