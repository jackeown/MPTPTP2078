%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:05 EST 2020

% Result     : Theorem 12.48s
% Output     : CNFRefutation 12.48s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  63 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [A_30,B_31] : k2_xboole_0(k4_xboole_0(A_30,B_31),A_30) = A_30 ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [B_31] : k4_xboole_0(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_6])).

tff(c_45,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_25] : k2_xboole_0(k1_xboole_0,A_25) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_6])).

tff(c_231,plain,(
    ! [A_33,B_34] : k4_xboole_0(k2_xboole_0(A_33,B_34),B_34) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_256,plain,(
    ! [A_25] : k4_xboole_0(k1_xboole_0,A_25) = k4_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_231])).

tff(c_274,plain,(
    ! [A_25] : k4_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_256])).

tff(c_353,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_381,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = k3_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_353])).

tff(c_397,plain,(
    ! [A_25] : k3_xboole_0(A_25,A_25) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_381])).

tff(c_596,plain,(
    ! [A_51,B_52,C_53] : k4_xboole_0(k3_xboole_0(A_51,B_52),C_53) = k3_xboole_0(A_51,k4_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_632,plain,(
    ! [A_25,C_53] : k3_xboole_0(A_25,k4_xboole_0(A_25,C_53)) = k4_xboole_0(A_25,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_596])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_262,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_231])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_453,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_496,plain,(
    ! [A_44,B_45,B_15] : k4_xboole_0(A_44,k2_xboole_0(B_45,k4_xboole_0(k4_xboole_0(A_44,B_45),B_15))) = k3_xboole_0(k4_xboole_0(A_44,B_45),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_453])).

tff(c_523,plain,(
    ! [A_44,B_45,B_15] : k4_xboole_0(A_44,k2_xboole_0(B_45,k4_xboole_0(A_44,k2_xboole_0(B_45,B_15)))) = k3_xboole_0(k4_xboole_0(A_44,B_45),B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_496])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_492,plain,(
    ! [A_14,B_15,C_46] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_46)) = k4_xboole_0(k3_xboole_0(A_14,B_15),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_453])).

tff(c_8279,plain,(
    ! [A_167,B_168,C_169] : k4_xboole_0(A_167,k2_xboole_0(k4_xboole_0(A_167,B_168),C_169)) = k3_xboole_0(A_167,k4_xboole_0(B_168,C_169)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_492])).

tff(c_44777,plain,(
    ! [A_440,B_441,B_442] : k4_xboole_0(A_440,k2_xboole_0(B_441,k4_xboole_0(A_440,B_442))) = k3_xboole_0(A_440,k4_xboole_0(B_442,B_441)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8279])).

tff(c_45231,plain,(
    ! [A_44,B_45,B_15] : k3_xboole_0(A_44,k4_xboole_0(k2_xboole_0(B_45,B_15),B_45)) = k3_xboole_0(k4_xboole_0(A_44,B_45),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_44777])).

tff(c_45498,plain,(
    ! [A_44,B_45,B_15] : k3_xboole_0(k4_xboole_0(A_44,B_45),B_15) = k3_xboole_0(A_44,k4_xboole_0(B_15,B_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_45231])).

tff(c_20,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_46224,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45498,c_21])).

tff(c_46239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_14,c_46224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:55:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.48/5.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.48/5.75  
% 12.48/5.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.48/5.76  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.48/5.76  
% 12.48/5.76  %Foreground sorts:
% 12.48/5.76  
% 12.48/5.76  
% 12.48/5.76  %Background operators:
% 12.48/5.76  
% 12.48/5.76  
% 12.48/5.76  %Foreground operators:
% 12.48/5.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.48/5.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.48/5.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.48/5.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.48/5.76  tff('#skF_2', type, '#skF_2': $i).
% 12.48/5.76  tff('#skF_3', type, '#skF_3': $i).
% 12.48/5.76  tff('#skF_1', type, '#skF_1': $i).
% 12.48/5.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.48/5.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.48/5.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.48/5.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.48/5.76  
% 12.48/5.77  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.48/5.77  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.48/5.77  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.48/5.77  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 12.48/5.77  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.48/5.77  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.48/5.77  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.48/5.77  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.48/5.77  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.48/5.77  tff(f_48, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 12.48/5.77  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.48/5.77  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.48/5.77  tff(c_92, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.48/5.77  tff(c_170, plain, (![A_30, B_31]: (k2_xboole_0(k4_xboole_0(A_30, B_31), A_30)=A_30)), inference(resolution, [status(thm)], [c_8, c_92])).
% 12.48/5.77  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.48/5.77  tff(c_183, plain, (![B_31]: (k4_xboole_0(k1_xboole_0, B_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_170, c_6])).
% 12.48/5.77  tff(c_45, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.48/5.77  tff(c_61, plain, (![A_25]: (k2_xboole_0(k1_xboole_0, A_25)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_45, c_6])).
% 12.48/5.77  tff(c_231, plain, (![A_33, B_34]: (k4_xboole_0(k2_xboole_0(A_33, B_34), B_34)=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.48/5.77  tff(c_256, plain, (![A_25]: (k4_xboole_0(k1_xboole_0, A_25)=k4_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_61, c_231])).
% 12.48/5.77  tff(c_274, plain, (![A_25]: (k4_xboole_0(A_25, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_256])).
% 12.48/5.77  tff(c_353, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.48/5.77  tff(c_381, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=k3_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_274, c_353])).
% 12.48/5.77  tff(c_397, plain, (![A_25]: (k3_xboole_0(A_25, A_25)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_381])).
% 12.48/5.77  tff(c_596, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k3_xboole_0(A_51, B_52), C_53)=k3_xboole_0(A_51, k4_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.48/5.77  tff(c_632, plain, (![A_25, C_53]: (k3_xboole_0(A_25, k4_xboole_0(A_25, C_53))=k4_xboole_0(A_25, C_53))), inference(superposition, [status(thm), theory('equality')], [c_397, c_596])).
% 12.48/5.77  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.48/5.77  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.48/5.77  tff(c_262, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_231])).
% 12.48/5.77  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.48/5.77  tff(c_453, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.48/5.77  tff(c_496, plain, (![A_44, B_45, B_15]: (k4_xboole_0(A_44, k2_xboole_0(B_45, k4_xboole_0(k4_xboole_0(A_44, B_45), B_15)))=k3_xboole_0(k4_xboole_0(A_44, B_45), B_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_453])).
% 12.48/5.77  tff(c_523, plain, (![A_44, B_45, B_15]: (k4_xboole_0(A_44, k2_xboole_0(B_45, k4_xboole_0(A_44, k2_xboole_0(B_45, B_15))))=k3_xboole_0(k4_xboole_0(A_44, B_45), B_15))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_496])).
% 12.48/5.77  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.48/5.77  tff(c_492, plain, (![A_14, B_15, C_46]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_46))=k4_xboole_0(k3_xboole_0(A_14, B_15), C_46))), inference(superposition, [status(thm), theory('equality')], [c_16, c_453])).
% 12.48/5.77  tff(c_8279, plain, (![A_167, B_168, C_169]: (k4_xboole_0(A_167, k2_xboole_0(k4_xboole_0(A_167, B_168), C_169))=k3_xboole_0(A_167, k4_xboole_0(B_168, C_169)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_492])).
% 12.48/5.77  tff(c_44777, plain, (![A_440, B_441, B_442]: (k4_xboole_0(A_440, k2_xboole_0(B_441, k4_xboole_0(A_440, B_442)))=k3_xboole_0(A_440, k4_xboole_0(B_442, B_441)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8279])).
% 12.48/5.77  tff(c_45231, plain, (![A_44, B_45, B_15]: (k3_xboole_0(A_44, k4_xboole_0(k2_xboole_0(B_45, B_15), B_45))=k3_xboole_0(k4_xboole_0(A_44, B_45), B_15))), inference(superposition, [status(thm), theory('equality')], [c_523, c_44777])).
% 12.48/5.77  tff(c_45498, plain, (![A_44, B_45, B_15]: (k3_xboole_0(k4_xboole_0(A_44, B_45), B_15)=k3_xboole_0(A_44, k4_xboole_0(B_15, B_45)))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_45231])).
% 12.48/5.77  tff(c_20, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.48/5.77  tff(c_21, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 12.48/5.77  tff(c_46224, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45498, c_21])).
% 12.48/5.77  tff(c_46239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_632, c_14, c_46224])).
% 12.48/5.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.48/5.77  
% 12.48/5.77  Inference rules
% 12.48/5.77  ----------------------
% 12.48/5.77  #Ref     : 0
% 12.48/5.77  #Sup     : 11623
% 12.48/5.77  #Fact    : 0
% 12.48/5.77  #Define  : 0
% 12.48/5.77  #Split   : 0
% 12.48/5.77  #Chain   : 0
% 12.48/5.77  #Close   : 0
% 12.48/5.77  
% 12.48/5.77  Ordering : KBO
% 12.48/5.77  
% 12.48/5.77  Simplification rules
% 12.48/5.77  ----------------------
% 12.48/5.77  #Subsume      : 13
% 12.48/5.77  #Demod        : 14403
% 12.48/5.77  #Tautology    : 8494
% 12.48/5.77  #SimpNegUnit  : 0
% 12.48/5.77  #BackRed      : 18
% 12.48/5.77  
% 12.48/5.77  #Partial instantiations: 0
% 12.48/5.77  #Strategies tried      : 1
% 12.48/5.77  
% 12.48/5.77  Timing (in seconds)
% 12.48/5.77  ----------------------
% 12.48/5.77  Preprocessing        : 0.27
% 12.48/5.77  Parsing              : 0.14
% 12.48/5.77  CNF conversion       : 0.01
% 12.48/5.77  Main loop            : 4.74
% 12.48/5.77  Inferencing          : 0.82
% 12.48/5.77  Reduction            : 2.83
% 12.48/5.77  Demodulation         : 2.57
% 12.48/5.77  BG Simplification    : 0.10
% 12.48/5.77  Subsumption          : 0.78
% 12.48/5.77  Abstraction          : 0.18
% 12.48/5.77  MUC search           : 0.00
% 12.48/5.77  Cooper               : 0.00
% 12.48/5.77  Total                : 5.04
% 12.48/5.77  Index Insertion      : 0.00
% 12.48/5.77  Index Deletion       : 0.00
% 12.48/5.77  Index Matching       : 0.00
% 12.48/5.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
