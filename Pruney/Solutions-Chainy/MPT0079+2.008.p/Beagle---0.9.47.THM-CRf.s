%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:43 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 125 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 149 expanded)
%              Number of equality atoms :   59 ( 108 expanded)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_36,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_381,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_388,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_381])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_417,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_432,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),A_54) = A_54 ),
    inference(resolution,[status(thm)],[c_22,c_417])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_438,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_2])).

tff(c_32,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_524,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | k4_xboole_0(A_60,B_61) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2678,plain,(
    ! [A_111,B_112] :
      ( k2_xboole_0(A_111,B_112) = B_112
      | k4_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_524,c_16])).

tff(c_2705,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2678])).

tff(c_2730,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_2705])).

tff(c_18,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_1112,plain,(
    ! [A_81,B_82,C_83] : k4_xboole_0(k4_xboole_0(A_81,B_82),C_83) = k4_xboole_0(A_81,k2_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_276,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_276])).

tff(c_1219,plain,(
    ! [C_84,B_85] : k4_xboole_0(C_84,k2_xboole_0(B_85,C_84)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_284])).

tff(c_1288,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_1219])).

tff(c_24,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11128,plain,(
    ! [C_210,A_211,B_212] : k2_xboole_0(C_210,k4_xboole_0(A_211,k2_xboole_0(B_212,C_210))) = k2_xboole_0(C_210,k4_xboole_0(A_211,B_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_24])).

tff(c_11366,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_11128])).

tff(c_11489,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11366])).

tff(c_11609,plain,
    ( k2_xboole_0('#skF_3','#skF_2') = '#skF_3'
    | k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2730,c_11489])).

tff(c_11637,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_4,c_11609])).

tff(c_26,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_389,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_381])).

tff(c_769,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6180,plain,(
    ! [A_184,B_185] : k4_xboole_0(A_184,k3_xboole_0(A_184,B_185)) = k3_xboole_0(A_184,k4_xboole_0(A_184,B_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_32])).

tff(c_6274,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_6180])).

tff(c_6319,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6274])).

tff(c_431,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(A_15,B_16),A_15) = A_15 ),
    inference(resolution,[status(thm)],[c_22,c_417])).

tff(c_1037,plain,(
    ! [A_79,B_80] : k2_xboole_0(k3_xboole_0(A_79,B_80),A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_431])).

tff(c_1083,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),B_4) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1037])).

tff(c_6366,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6319,c_1083])).

tff(c_6395,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_6366])).

tff(c_1147,plain,(
    ! [C_83,B_82] : k4_xboole_0(C_83,k2_xboole_0(B_82,C_83)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_284])).

tff(c_11776,plain,(
    ! [A_213] : k2_xboole_0('#skF_2',k4_xboole_0(A_213,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_213,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_11128])).

tff(c_11926,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_11776])).

tff(c_11988,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11637,c_2,c_6395,c_18,c_11926])).

tff(c_11990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_11988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:12:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.03/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.94  
% 8.03/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.94  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.03/2.94  
% 8.03/2.94  %Foreground sorts:
% 8.03/2.94  
% 8.03/2.94  
% 8.03/2.94  %Background operators:
% 8.03/2.94  
% 8.03/2.94  
% 8.03/2.94  %Foreground operators:
% 8.03/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.03/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.03/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.03/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.03/2.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.03/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.03/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.03/2.94  tff('#skF_1', type, '#skF_1': $i).
% 8.03/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.03/2.94  tff('#skF_4', type, '#skF_4': $i).
% 8.03/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.03/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.03/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.03/2.94  
% 8.03/2.96  tff(f_70, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.03/2.96  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.03/2.96  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.03/2.96  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.03/2.96  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.03/2.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.03/2.96  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.03/2.96  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.03/2.96  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.03/2.96  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.03/2.96  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.03/2.96  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.03/2.96  tff(c_36, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/2.96  tff(c_38, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/2.96  tff(c_381, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/2.96  tff(c_388, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_381])).
% 8.03/2.96  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.03/2.96  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.03/2.96  tff(c_417, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.96  tff(c_432, plain, (![A_54, B_55]: (k2_xboole_0(k4_xboole_0(A_54, B_55), A_54)=A_54)), inference(resolution, [status(thm)], [c_22, c_417])).
% 8.03/2.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.03/2.96  tff(c_438, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k4_xboole_0(A_54, B_55))=A_54)), inference(superposition, [status(thm), theory('equality')], [c_432, c_2])).
% 8.03/2.96  tff(c_32, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.03/2.96  tff(c_524, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | k4_xboole_0(A_60, B_61)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.96  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.96  tff(c_2678, plain, (![A_111, B_112]: (k2_xboole_0(A_111, B_112)=B_112 | k4_xboole_0(A_111, B_112)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_524, c_16])).
% 8.03/2.96  tff(c_2705, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_2678])).
% 8.03/2.96  tff(c_2730, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_438, c_2705])).
% 8.03/2.96  tff(c_18, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.03/2.96  tff(c_42, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/2.96  tff(c_43, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 8.03/2.96  tff(c_1112, plain, (![A_81, B_82, C_83]: (k4_xboole_0(k4_xboole_0(A_81, B_82), C_83)=k4_xboole_0(A_81, k2_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.03/2.96  tff(c_276, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.96  tff(c_284, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_276])).
% 8.03/2.96  tff(c_1219, plain, (![C_84, B_85]: (k4_xboole_0(C_84, k2_xboole_0(B_85, C_84))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1112, c_284])).
% 8.03/2.96  tff(c_1288, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_43, c_1219])).
% 8.03/2.96  tff(c_24, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.03/2.96  tff(c_11128, plain, (![C_210, A_211, B_212]: (k2_xboole_0(C_210, k4_xboole_0(A_211, k2_xboole_0(B_212, C_210)))=k2_xboole_0(C_210, k4_xboole_0(A_211, B_212)))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_24])).
% 8.03/2.96  tff(c_11366, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1288, c_11128])).
% 8.03/2.96  tff(c_11489, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11366])).
% 8.03/2.96  tff(c_11609, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3' | k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2730, c_11489])).
% 8.03/2.96  tff(c_11637, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_4, c_11609])).
% 8.03/2.96  tff(c_26, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.03/2.96  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/2.96  tff(c_389, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_381])).
% 8.03/2.96  tff(c_769, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.03/2.96  tff(c_6180, plain, (![A_184, B_185]: (k4_xboole_0(A_184, k3_xboole_0(A_184, B_185))=k3_xboole_0(A_184, k4_xboole_0(A_184, B_185)))), inference(superposition, [status(thm), theory('equality')], [c_769, c_32])).
% 8.03/2.96  tff(c_6274, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_389, c_6180])).
% 8.03/2.96  tff(c_6319, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6274])).
% 8.03/2.96  tff(c_431, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(A_15, B_16), A_15)=A_15)), inference(resolution, [status(thm)], [c_22, c_417])).
% 8.03/2.96  tff(c_1037, plain, (![A_79, B_80]: (k2_xboole_0(k3_xboole_0(A_79, B_80), A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_769, c_431])).
% 8.03/2.96  tff(c_1083, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), B_4)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1037])).
% 8.03/2.96  tff(c_6366, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6319, c_1083])).
% 8.03/2.96  tff(c_6395, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_6366])).
% 8.03/2.96  tff(c_1147, plain, (![C_83, B_82]: (k4_xboole_0(C_83, k2_xboole_0(B_82, C_83))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1112, c_284])).
% 8.03/2.96  tff(c_11776, plain, (![A_213]: (k2_xboole_0('#skF_2', k4_xboole_0(A_213, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_213, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_43, c_11128])).
% 8.03/2.96  tff(c_11926, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1147, c_11776])).
% 8.03/2.96  tff(c_11988, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11637, c_2, c_6395, c_18, c_11926])).
% 8.03/2.96  tff(c_11990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_11988])).
% 8.03/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.96  
% 8.03/2.96  Inference rules
% 8.03/2.96  ----------------------
% 8.03/2.96  #Ref     : 0
% 8.03/2.96  #Sup     : 2995
% 8.03/2.96  #Fact    : 0
% 8.03/2.96  #Define  : 0
% 8.03/2.96  #Split   : 3
% 8.03/2.96  #Chain   : 0
% 8.03/2.96  #Close   : 0
% 8.03/2.96  
% 8.03/2.96  Ordering : KBO
% 8.03/2.96  
% 8.03/2.96  Simplification rules
% 8.03/2.96  ----------------------
% 8.03/2.96  #Subsume      : 43
% 8.03/2.96  #Demod        : 3128
% 8.03/2.96  #Tautology    : 1825
% 8.03/2.96  #SimpNegUnit  : 3
% 8.03/2.96  #BackRed      : 4
% 8.03/2.96  
% 8.03/2.96  #Partial instantiations: 0
% 8.03/2.96  #Strategies tried      : 1
% 8.03/2.96  
% 8.03/2.96  Timing (in seconds)
% 8.03/2.96  ----------------------
% 8.03/2.96  Preprocessing        : 0.30
% 8.03/2.96  Parsing              : 0.16
% 8.03/2.96  CNF conversion       : 0.02
% 8.03/2.96  Main loop            : 1.90
% 8.03/2.96  Inferencing          : 0.39
% 8.03/2.96  Reduction            : 1.09
% 8.03/2.96  Demodulation         : 0.96
% 8.03/2.96  BG Simplification    : 0.05
% 8.03/2.96  Subsumption          : 0.27
% 8.03/2.96  Abstraction          : 0.07
% 8.03/2.96  MUC search           : 0.00
% 8.03/2.96  Cooper               : 0.00
% 8.03/2.96  Total                : 2.23
% 8.03/2.96  Index Insertion      : 0.00
% 8.03/2.96  Index Deletion       : 0.00
% 8.03/2.96  Index Matching       : 0.00
% 8.03/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
