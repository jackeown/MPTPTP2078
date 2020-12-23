%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 122 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 152 expanded)
%              Number of equality atoms :   40 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_139,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_24,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_58,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [A_39] : k3_xboole_0(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_490,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_xboole_0(A_67,C_68)
      | ~ r1_xboole_0(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2108,plain,(
    ! [A_126,B_127,A_128] :
      ( r1_xboole_0(A_126,B_127)
      | ~ r1_tarski(A_126,k4_xboole_0(A_128,B_127)) ) ),
    inference(resolution,[status(thm)],[c_26,c_490])).

tff(c_2164,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_2108])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2175,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2164,c_4])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_297,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_324,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_297])).

tff(c_327,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_324])).

tff(c_230,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_254,plain,(
    ! [A_54] : r1_tarski(A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_14])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_258,plain,(
    ! [A_54] : k3_xboole_0(A_54,A_54) = A_54 ),
    inference(resolution,[status(thm)],[c_254,c_10])).

tff(c_363,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_372,plain,(
    ! [A_54] : k5_xboole_0(A_54,A_54) = k4_xboole_0(A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_363])).

tff(c_396,plain,(
    ! [A_54] : k5_xboole_0(A_54,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_372])).

tff(c_203,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_211,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_203])).

tff(c_375,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_363])).

tff(c_580,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_375])).

tff(c_1187,plain,(
    ! [A_99,B_100,C_101] : k2_xboole_0(k4_xboole_0(A_99,B_100),k3_xboole_0(A_99,C_101)) = k4_xboole_0(A_99,k4_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_29,B_30] : k5_xboole_0(k5_xboole_0(A_29,B_30),k2_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_11653,plain,(
    ! [A_272,B_273,C_274] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_272,B_273),k3_xboole_0(A_272,C_274)),k4_xboole_0(A_272,k4_xboole_0(B_273,C_274))) = k3_xboole_0(k4_xboole_0(A_272,B_273),k3_xboole_0(A_272,C_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_34])).

tff(c_11896,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_11653])).

tff(c_12019,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2175,c_20,c_20,c_2175,c_2,c_11896])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12136,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12019,c_16])).

tff(c_12188,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_12136])).

tff(c_507,plain,(
    ! [A_70,B_71] : r1_tarski(k3_xboole_0(A_70,B_71),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_14])).

tff(c_528,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_507])).

tff(c_12263,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12188,c_528])).

tff(c_12291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_12263])).

tff(c_12292,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_12910,plain,(
    ! [A_309,C_310,B_311] :
      ( r1_xboole_0(A_309,C_310)
      | ~ r1_xboole_0(B_311,C_310)
      | ~ r1_tarski(A_309,B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14398,plain,(
    ! [A_356,B_357,A_358] :
      ( r1_xboole_0(A_356,B_357)
      | ~ r1_tarski(A_356,k4_xboole_0(A_358,B_357)) ) ),
    inference(resolution,[status(thm)],[c_26,c_12910])).

tff(c_14445,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_14398])).

tff(c_14457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12292,c_14445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.97  
% 7.50/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.97  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.50/2.97  
% 7.50/2.97  %Foreground sorts:
% 7.50/2.97  
% 7.50/2.97  
% 7.50/2.97  %Background operators:
% 7.50/2.97  
% 7.50/2.97  
% 7.50/2.97  %Foreground operators:
% 7.50/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.50/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.50/2.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.50/2.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.50/2.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.50/2.97  tff('#skF_2', type, '#skF_2': $i).
% 7.50/2.97  tff('#skF_3', type, '#skF_3': $i).
% 7.50/2.97  tff('#skF_1', type, '#skF_1': $i).
% 7.50/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.50/2.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.50/2.97  
% 7.50/2.98  tff(f_72, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.50/2.98  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.50/2.98  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.50/2.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.50/2.98  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.50/2.98  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.50/2.98  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.50/2.98  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.50/2.98  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.50/2.98  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.50/2.98  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.50/2.98  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.50/2.98  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.50/2.98  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 7.50/2.98  tff(f_65, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.50/2.98  tff(c_36, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.50/2.98  tff(c_139, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 7.50/2.98  tff(c_24, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.50/2.98  tff(c_217, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.50/2.98  tff(c_229, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(resolution, [status(thm)], [c_24, c_217])).
% 7.50/2.98  tff(c_58, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.50/2.98  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.50/2.98  tff(c_74, plain, (![A_39]: (k3_xboole_0(k1_xboole_0, A_39)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_12])).
% 7.50/2.98  tff(c_38, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.50/2.98  tff(c_26, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.50/2.98  tff(c_490, plain, (![A_67, C_68, B_69]: (r1_xboole_0(A_67, C_68) | ~r1_xboole_0(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.50/2.98  tff(c_2108, plain, (![A_126, B_127, A_128]: (r1_xboole_0(A_126, B_127) | ~r1_tarski(A_126, k4_xboole_0(A_128, B_127)))), inference(resolution, [status(thm)], [c_26, c_490])).
% 7.50/2.98  tff(c_2164, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_2108])).
% 7.50/2.98  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.50/2.98  tff(c_2175, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2164, c_4])).
% 7.50/2.98  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.50/2.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.50/2.98  tff(c_297, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.50/2.98  tff(c_324, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_229, c_297])).
% 7.50/2.98  tff(c_327, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_324])).
% 7.50/2.98  tff(c_230, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=A_53)), inference(resolution, [status(thm)], [c_24, c_217])).
% 7.50/2.98  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.50/2.98  tff(c_254, plain, (![A_54]: (r1_tarski(A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_230, c_14])).
% 7.50/2.98  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.50/2.98  tff(c_258, plain, (![A_54]: (k3_xboole_0(A_54, A_54)=A_54)), inference(resolution, [status(thm)], [c_254, c_10])).
% 7.50/2.98  tff(c_363, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.50/2.98  tff(c_372, plain, (![A_54]: (k5_xboole_0(A_54, A_54)=k4_xboole_0(A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_258, c_363])).
% 7.50/2.98  tff(c_396, plain, (![A_54]: (k5_xboole_0(A_54, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_372])).
% 7.50/2.98  tff(c_203, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.50/2.98  tff(c_211, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_38, c_203])).
% 7.50/2.98  tff(c_375, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_211, c_363])).
% 7.50/2.98  tff(c_580, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_396, c_375])).
% 7.50/2.98  tff(c_1187, plain, (![A_99, B_100, C_101]: (k2_xboole_0(k4_xboole_0(A_99, B_100), k3_xboole_0(A_99, C_101))=k4_xboole_0(A_99, k4_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.50/2.98  tff(c_34, plain, (![A_29, B_30]: (k5_xboole_0(k5_xboole_0(A_29, B_30), k2_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.50/2.98  tff(c_11653, plain, (![A_272, B_273, C_274]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_272, B_273), k3_xboole_0(A_272, C_274)), k4_xboole_0(A_272, k4_xboole_0(B_273, C_274)))=k3_xboole_0(k4_xboole_0(A_272, B_273), k3_xboole_0(A_272, C_274)))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_34])).
% 7.50/2.98  tff(c_11896, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3')), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_580, c_11653])).
% 7.50/2.98  tff(c_12019, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2175, c_20, c_20, c_2175, c_2, c_11896])).
% 7.50/2.98  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.50/2.98  tff(c_12136, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12019, c_16])).
% 7.50/2.98  tff(c_12188, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_12136])).
% 7.50/2.98  tff(c_507, plain, (![A_70, B_71]: (r1_tarski(k3_xboole_0(A_70, B_71), A_70))), inference(superposition, [status(thm), theory('equality')], [c_297, c_14])).
% 7.50/2.98  tff(c_528, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_507])).
% 7.50/2.98  tff(c_12263, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12188, c_528])).
% 7.50/2.98  tff(c_12291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_12263])).
% 7.50/2.98  tff(c_12292, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 7.50/2.98  tff(c_12910, plain, (![A_309, C_310, B_311]: (r1_xboole_0(A_309, C_310) | ~r1_xboole_0(B_311, C_310) | ~r1_tarski(A_309, B_311))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.50/2.98  tff(c_14398, plain, (![A_356, B_357, A_358]: (r1_xboole_0(A_356, B_357) | ~r1_tarski(A_356, k4_xboole_0(A_358, B_357)))), inference(resolution, [status(thm)], [c_26, c_12910])).
% 7.50/2.98  tff(c_14445, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_14398])).
% 7.50/2.98  tff(c_14457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12292, c_14445])).
% 7.50/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.98  
% 7.50/2.98  Inference rules
% 7.50/2.98  ----------------------
% 7.50/2.98  #Ref     : 0
% 7.50/2.98  #Sup     : 3625
% 7.50/2.98  #Fact    : 0
% 7.50/2.98  #Define  : 0
% 7.50/2.98  #Split   : 3
% 7.50/2.98  #Chain   : 0
% 7.50/2.98  #Close   : 0
% 7.50/2.98  
% 7.50/2.98  Ordering : KBO
% 7.50/2.98  
% 7.50/2.98  Simplification rules
% 7.50/2.98  ----------------------
% 7.50/2.98  #Subsume      : 57
% 7.50/2.98  #Demod        : 3544
% 7.50/2.98  #Tautology    : 2389
% 7.50/2.98  #SimpNegUnit  : 5
% 7.50/2.98  #BackRed      : 9
% 7.50/2.98  
% 7.50/2.98  #Partial instantiations: 0
% 7.50/2.98  #Strategies tried      : 1
% 7.50/2.98  
% 7.50/2.98  Timing (in seconds)
% 7.50/2.98  ----------------------
% 7.77/2.99  Preprocessing        : 0.30
% 7.77/2.99  Parsing              : 0.17
% 7.77/2.99  CNF conversion       : 0.02
% 7.77/2.99  Main loop            : 1.91
% 7.77/2.99  Inferencing          : 0.47
% 7.77/2.99  Reduction            : 0.95
% 7.77/2.99  Demodulation         : 0.80
% 7.77/2.99  BG Simplification    : 0.06
% 7.77/2.99  Subsumption          : 0.31
% 7.77/2.99  Abstraction          : 0.08
% 7.77/2.99  MUC search           : 0.00
% 7.77/2.99  Cooper               : 0.00
% 7.77/2.99  Total                : 2.24
% 7.77/2.99  Index Insertion      : 0.00
% 7.77/2.99  Index Deletion       : 0.00
% 7.77/2.99  Index Matching       : 0.00
% 7.77/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
