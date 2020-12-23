%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:22 EST 2020

% Result     : Theorem 12.46s
% Output     : CNFRefutation 12.46s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 117 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 119 expanded)
%              Number of equality atoms :   49 (  90 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_106,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_26])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [A_42,B_43] : k4_xboole_0(k2_xboole_0(A_42,B_43),B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k2_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_14])).

tff(c_245,plain,(
    ! [A_42] : k2_xboole_0(A_42,k1_xboole_0) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_226])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_157])).

tff(c_390,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_424,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_390])).

tff(c_438,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_424])).

tff(c_1061,plain,(
    ! [A_73,B_74,C_75] : k4_xboole_0(k4_xboole_0(A_73,B_74),C_75) = k4_xboole_0(A_73,k2_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1137,plain,(
    ! [C_75] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_75)) = k4_xboole_0('#skF_1',C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_1061])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_43])).

tff(c_264,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_295,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_264])).

tff(c_311,plain,(
    ! [A_5,B_6] : k3_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k4_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_295])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_564,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k3_xboole_0(A_59,B_60),C_61) = k3_xboole_0(A_59,k4_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_442,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_458,plain,(
    ! [A_53,B_54] : k4_xboole_0(k3_xboole_0(A_53,B_54),A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_442,c_8])).

tff(c_571,plain,(
    ! [C_61,B_60] : k3_xboole_0(C_61,k4_xboole_0(B_60,C_61)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_458])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),C_21) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_622,plain,(
    ! [A_59,B_60,B_18] : k3_xboole_0(A_59,k4_xboole_0(B_60,k4_xboole_0(k3_xboole_0(A_59,B_60),B_18))) = k3_xboole_0(k3_xboole_0(A_59,B_60),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_564])).

tff(c_38247,plain,(
    ! [A_337,B_338,B_339] : k3_xboole_0(A_337,k4_xboole_0(B_338,k3_xboole_0(A_337,k4_xboole_0(B_338,B_339)))) = k3_xboole_0(k3_xboole_0(A_337,B_338),B_339) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_622])).

tff(c_38689,plain,(
    ! [B_338,B_339,B_6] : k3_xboole_0(k4_xboole_0(k4_xboole_0(B_338,B_339),B_6),k4_xboole_0(B_338,k4_xboole_0(k4_xboole_0(B_338,B_339),B_6))) = k3_xboole_0(k3_xboole_0(k4_xboole_0(k4_xboole_0(B_338,B_339),B_6),B_338),B_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_38247])).

tff(c_39558,plain,(
    ! [B_343,B_344,B_345] : k3_xboole_0(k4_xboole_0(B_343,k2_xboole_0(B_344,B_345)),B_344) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_18,c_571,c_38689])).

tff(c_40950,plain,(
    ! [C_349] : k3_xboole_0(k4_xboole_0('#skF_1',C_349),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_39558])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_585,plain,(
    ! [C_61,A_59,B_60] : k2_xboole_0(C_61,k3_xboole_0(A_59,k4_xboole_0(B_60,C_61))) = k2_xboole_0(C_61,k3_xboole_0(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_12])).

tff(c_41027,plain,(
    ! [C_349] : k2_xboole_0('#skF_3',k3_xboole_0(k4_xboole_0('#skF_1',C_349),'#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40950,c_585])).

tff(c_49224,plain,(
    ! [C_380] : k2_xboole_0('#skF_3',k3_xboole_0(k4_xboole_0('#skF_1',C_380),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_41027])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1087,plain,(
    ! [A_73,B_74,B_16] : k4_xboole_0(A_73,k2_xboole_0(B_74,k3_xboole_0(k4_xboole_0(A_73,B_74),B_16))) = k4_xboole_0(k4_xboole_0(A_73,B_74),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_20])).

tff(c_1180,plain,(
    ! [A_73,B_74,B_16] : k4_xboole_0(A_73,k2_xboole_0(B_74,k3_xboole_0(k4_xboole_0(A_73,B_74),B_16))) = k4_xboole_0(A_73,k2_xboole_0(B_74,B_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1087])).

tff(c_49230,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_49224,c_1180])).

tff(c_1083,plain,(
    ! [C_75,A_73,B_74] : k3_xboole_0(C_75,k4_xboole_0(A_73,k2_xboole_0(B_74,C_75))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_571])).

tff(c_53695,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49230,c_1083])).

tff(c_53795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_53695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.46/6.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.46/6.38  
% 12.46/6.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.46/6.38  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.46/6.38  
% 12.46/6.38  %Foreground sorts:
% 12.46/6.38  
% 12.46/6.38  
% 12.46/6.38  %Background operators:
% 12.46/6.38  
% 12.46/6.38  
% 12.46/6.38  %Foreground operators:
% 12.46/6.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.46/6.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.46/6.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.46/6.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.46/6.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.46/6.38  tff('#skF_2', type, '#skF_2': $i).
% 12.46/6.38  tff('#skF_3', type, '#skF_3': $i).
% 12.46/6.38  tff('#skF_1', type, '#skF_1': $i).
% 12.46/6.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.46/6.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.46/6.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.46/6.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.46/6.38  
% 12.46/6.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.46/6.40  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 12.46/6.40  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.46/6.40  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.46/6.40  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.46/6.40  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.46/6.40  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.46/6.40  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.46/6.40  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.46/6.40  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.46/6.40  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.46/6.40  tff(c_106, plain, (![A_31, B_32]: (r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.46/6.40  tff(c_26, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.46/6.40  tff(c_110, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_26])).
% 12.46/6.40  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.46/6.40  tff(c_210, plain, (![A_42, B_43]: (k4_xboole_0(k2_xboole_0(A_42, B_43), B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.46/6.40  tff(c_226, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k2_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_210, c_14])).
% 12.46/6.40  tff(c_245, plain, (![A_42]: (k2_xboole_0(A_42, k1_xboole_0)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_226])).
% 12.46/6.40  tff(c_28, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.46/6.40  tff(c_157, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.46/6.40  tff(c_165, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_157])).
% 12.46/6.40  tff(c_390, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.46/6.40  tff(c_424, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_165, c_390])).
% 12.46/6.40  tff(c_438, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_424])).
% 12.46/6.40  tff(c_1061, plain, (![A_73, B_74, C_75]: (k4_xboole_0(k4_xboole_0(A_73, B_74), C_75)=k4_xboole_0(A_73, k2_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.46/6.40  tff(c_1137, plain, (![C_75]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_75))=k4_xboole_0('#skF_1', C_75))), inference(superposition, [status(thm), theory('equality')], [c_438, c_1061])).
% 12.46/6.40  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.46/6.40  tff(c_43, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.46/6.40  tff(c_51, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_43])).
% 12.46/6.40  tff(c_264, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.46/6.40  tff(c_295, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_51, c_264])).
% 12.46/6.40  tff(c_311, plain, (![A_5, B_6]: (k3_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k4_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_295])).
% 12.46/6.40  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.46/6.40  tff(c_564, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k3_xboole_0(A_59, B_60), C_61)=k3_xboole_0(A_59, k4_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.46/6.40  tff(c_442, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_264, c_10])).
% 12.46/6.40  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.46/6.40  tff(c_458, plain, (![A_53, B_54]: (k4_xboole_0(k3_xboole_0(A_53, B_54), A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_442, c_8])).
% 12.46/6.40  tff(c_571, plain, (![C_61, B_60]: (k3_xboole_0(C_61, k4_xboole_0(B_60, C_61))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_564, c_458])).
% 12.46/6.40  tff(c_24, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), C_21)=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.46/6.40  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.46/6.40  tff(c_622, plain, (![A_59, B_60, B_18]: (k3_xboole_0(A_59, k4_xboole_0(B_60, k4_xboole_0(k3_xboole_0(A_59, B_60), B_18)))=k3_xboole_0(k3_xboole_0(A_59, B_60), B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_564])).
% 12.46/6.40  tff(c_38247, plain, (![A_337, B_338, B_339]: (k3_xboole_0(A_337, k4_xboole_0(B_338, k3_xboole_0(A_337, k4_xboole_0(B_338, B_339))))=k3_xboole_0(k3_xboole_0(A_337, B_338), B_339))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_622])).
% 12.46/6.40  tff(c_38689, plain, (![B_338, B_339, B_6]: (k3_xboole_0(k4_xboole_0(k4_xboole_0(B_338, B_339), B_6), k4_xboole_0(B_338, k4_xboole_0(k4_xboole_0(B_338, B_339), B_6)))=k3_xboole_0(k3_xboole_0(k4_xboole_0(k4_xboole_0(B_338, B_339), B_6), B_338), B_339))), inference(superposition, [status(thm), theory('equality')], [c_311, c_38247])).
% 12.46/6.40  tff(c_39558, plain, (![B_343, B_344, B_345]: (k3_xboole_0(k4_xboole_0(B_343, k2_xboole_0(B_344, B_345)), B_344)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_311, c_18, c_571, c_38689])).
% 12.46/6.40  tff(c_40950, plain, (![C_349]: (k3_xboole_0(k4_xboole_0('#skF_1', C_349), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1137, c_39558])).
% 12.46/6.40  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.46/6.40  tff(c_585, plain, (![C_61, A_59, B_60]: (k2_xboole_0(C_61, k3_xboole_0(A_59, k4_xboole_0(B_60, C_61)))=k2_xboole_0(C_61, k3_xboole_0(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_564, c_12])).
% 12.46/6.40  tff(c_41027, plain, (![C_349]: (k2_xboole_0('#skF_3', k3_xboole_0(k4_xboole_0('#skF_1', C_349), '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40950, c_585])).
% 12.46/6.40  tff(c_49224, plain, (![C_380]: (k2_xboole_0('#skF_3', k3_xboole_0(k4_xboole_0('#skF_1', C_380), '#skF_2'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_41027])).
% 12.46/6.40  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.46/6.40  tff(c_1087, plain, (![A_73, B_74, B_16]: (k4_xboole_0(A_73, k2_xboole_0(B_74, k3_xboole_0(k4_xboole_0(A_73, B_74), B_16)))=k4_xboole_0(k4_xboole_0(A_73, B_74), B_16))), inference(superposition, [status(thm), theory('equality')], [c_1061, c_20])).
% 12.46/6.40  tff(c_1180, plain, (![A_73, B_74, B_16]: (k4_xboole_0(A_73, k2_xboole_0(B_74, k3_xboole_0(k4_xboole_0(A_73, B_74), B_16)))=k4_xboole_0(A_73, k2_xboole_0(B_74, B_16)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1087])).
% 12.46/6.40  tff(c_49230, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_49224, c_1180])).
% 12.46/6.40  tff(c_1083, plain, (![C_75, A_73, B_74]: (k3_xboole_0(C_75, k4_xboole_0(A_73, k2_xboole_0(B_74, C_75)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1061, c_571])).
% 12.46/6.40  tff(c_53695, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_49230, c_1083])).
% 12.46/6.40  tff(c_53795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_53695])).
% 12.46/6.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.46/6.40  
% 12.46/6.40  Inference rules
% 12.46/6.40  ----------------------
% 12.46/6.40  #Ref     : 0
% 12.46/6.40  #Sup     : 13388
% 12.46/6.40  #Fact    : 0
% 12.46/6.40  #Define  : 0
% 12.46/6.40  #Split   : 0
% 12.46/6.40  #Chain   : 0
% 12.46/6.40  #Close   : 0
% 12.46/6.40  
% 12.46/6.40  Ordering : KBO
% 12.46/6.40  
% 12.46/6.40  Simplification rules
% 12.46/6.40  ----------------------
% 12.46/6.40  #Subsume      : 0
% 12.46/6.40  #Demod        : 15910
% 12.46/6.40  #Tautology    : 10132
% 12.46/6.40  #SimpNegUnit  : 1
% 12.46/6.40  #BackRed      : 2
% 12.46/6.40  
% 12.46/6.40  #Partial instantiations: 0
% 12.46/6.40  #Strategies tried      : 1
% 12.46/6.40  
% 12.46/6.40  Timing (in seconds)
% 12.46/6.40  ----------------------
% 12.46/6.40  Preprocessing        : 0.28
% 12.46/6.40  Parsing              : 0.15
% 12.46/6.40  CNF conversion       : 0.02
% 12.46/6.40  Main loop            : 5.36
% 12.46/6.40  Inferencing          : 0.90
% 12.46/6.40  Reduction            : 3.20
% 12.46/6.40  Demodulation         : 2.89
% 12.46/6.40  BG Simplification    : 0.10
% 12.46/6.40  Subsumption          : 0.95
% 12.46/6.40  Abstraction          : 0.20
% 12.46/6.40  MUC search           : 0.00
% 12.46/6.40  Cooper               : 0.00
% 12.46/6.40  Total                : 5.67
% 12.46/6.40  Index Insertion      : 0.00
% 12.46/6.40  Index Deletion       : 0.00
% 12.46/6.40  Index Matching       : 0.00
% 12.46/6.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
