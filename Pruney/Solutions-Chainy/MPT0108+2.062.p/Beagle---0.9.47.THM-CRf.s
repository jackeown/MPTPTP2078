%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:06 EST 2020

% Result     : Theorem 39.33s
% Output     : CNFRefutation 39.33s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  39 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_389,plain,(
    ! [A_40,B_41,C_42] : k5_xboole_0(k5_xboole_0(A_40,B_41),C_42) = k5_xboole_0(A_40,k5_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7906,plain,(
    ! [A_179,B_180,C_181] : k5_xboole_0(A_179,k5_xboole_0(k3_xboole_0(A_179,B_180),C_181)) = k5_xboole_0(k4_xboole_0(A_179,B_180),C_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_389])).

tff(c_8044,plain,(
    ! [A_179,B_180,B_2] : k5_xboole_0(k4_xboole_0(A_179,B_180),k3_xboole_0(B_2,k3_xboole_0(A_179,B_180))) = k5_xboole_0(A_179,k4_xboole_0(k3_xboole_0(A_179,B_180),B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_7906])).

tff(c_8105,plain,(
    ! [A_179,B_180,B_2] : k5_xboole_0(k4_xboole_0(A_179,B_180),k3_xboole_0(B_2,k3_xboole_0(A_179,B_180))) = k4_xboole_0(A_179,k4_xboole_0(B_180,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12,c_8044])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11223,plain,(
    ! [A_209,B_210,B_211] : k5_xboole_0(A_209,k5_xboole_0(B_210,k3_xboole_0(k5_xboole_0(A_209,B_210),B_211))) = k4_xboole_0(k5_xboole_0(A_209,B_210),B_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_389])).

tff(c_11456,plain,(
    ! [A_17,B_18,B_211] : k5_xboole_0(A_17,k5_xboole_0(k4_xboole_0(B_18,A_17),k3_xboole_0(k2_xboole_0(A_17,B_18),B_211))) = k4_xboole_0(k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)),B_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_11223])).

tff(c_68947,plain,(
    ! [A_534,B_535,B_536] : k5_xboole_0(A_534,k5_xboole_0(k4_xboole_0(B_535,A_534),k3_xboole_0(k2_xboole_0(A_534,B_535),B_536))) = k4_xboole_0(k2_xboole_0(A_534,B_535),B_536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11456])).

tff(c_69088,plain,(
    ! [B_180,A_179] : k5_xboole_0(B_180,k4_xboole_0(A_179,k4_xboole_0(B_180,k2_xboole_0(B_180,A_179)))) = k4_xboole_0(k2_xboole_0(B_180,A_179),k3_xboole_0(A_179,B_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8105,c_68947])).

tff(c_96836,plain,(
    ! [B_641,A_642] : k4_xboole_0(k2_xboole_0(B_641,A_642),k3_xboole_0(A_642,B_641)) = k5_xboole_0(B_641,A_642) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_69088])).

tff(c_97448,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),k3_xboole_0(B_2,A_1)) = k5_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96836])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_136334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97448,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 13:07:36 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.33/30.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.33/30.54  
% 39.33/30.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.33/30.55  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 39.33/30.55  
% 39.33/30.55  %Foreground sorts:
% 39.33/30.55  
% 39.33/30.55  
% 39.33/30.55  %Background operators:
% 39.33/30.55  
% 39.33/30.55  
% 39.33/30.55  %Foreground operators:
% 39.33/30.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.33/30.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 39.33/30.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 39.33/30.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 39.33/30.55  tff('#skF_2', type, '#skF_2': $i).
% 39.33/30.55  tff('#skF_1', type, '#skF_1': $i).
% 39.33/30.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.33/30.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.33/30.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.33/30.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.33/30.55  
% 39.33/30.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 39.33/30.56  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 39.33/30.56  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 39.33/30.56  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 39.33/30.56  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 39.33/30.56  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 39.33/30.56  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 39.33/30.56  tff(f_46, negated_conjecture, ~(![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 39.33/30.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 39.33/30.56  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.33/30.56  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 39.33/30.56  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 39.33/30.56  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 39.33/30.56  tff(c_95, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 39.33/30.56  tff(c_104, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 39.33/30.56  tff(c_389, plain, (![A_40, B_41, C_42]: (k5_xboole_0(k5_xboole_0(A_40, B_41), C_42)=k5_xboole_0(A_40, k5_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.33/30.56  tff(c_7906, plain, (![A_179, B_180, C_181]: (k5_xboole_0(A_179, k5_xboole_0(k3_xboole_0(A_179, B_180), C_181))=k5_xboole_0(k4_xboole_0(A_179, B_180), C_181))), inference(superposition, [status(thm), theory('equality')], [c_4, c_389])).
% 39.33/30.56  tff(c_8044, plain, (![A_179, B_180, B_2]: (k5_xboole_0(k4_xboole_0(A_179, B_180), k3_xboole_0(B_2, k3_xboole_0(A_179, B_180)))=k5_xboole_0(A_179, k4_xboole_0(k3_xboole_0(A_179, B_180), B_2)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_7906])).
% 39.33/30.56  tff(c_8105, plain, (![A_179, B_180, B_2]: (k5_xboole_0(k4_xboole_0(A_179, B_180), k3_xboole_0(B_2, k3_xboole_0(A_179, B_180)))=k4_xboole_0(A_179, k4_xboole_0(B_180, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12, c_8044])).
% 39.33/30.56  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 39.33/30.56  tff(c_11223, plain, (![A_209, B_210, B_211]: (k5_xboole_0(A_209, k5_xboole_0(B_210, k3_xboole_0(k5_xboole_0(A_209, B_210), B_211)))=k4_xboole_0(k5_xboole_0(A_209, B_210), B_211))), inference(superposition, [status(thm), theory('equality')], [c_4, c_389])).
% 39.33/30.56  tff(c_11456, plain, (![A_17, B_18, B_211]: (k5_xboole_0(A_17, k5_xboole_0(k4_xboole_0(B_18, A_17), k3_xboole_0(k2_xboole_0(A_17, B_18), B_211)))=k4_xboole_0(k5_xboole_0(A_17, k4_xboole_0(B_18, A_17)), B_211))), inference(superposition, [status(thm), theory('equality')], [c_18, c_11223])).
% 39.33/30.56  tff(c_68947, plain, (![A_534, B_535, B_536]: (k5_xboole_0(A_534, k5_xboole_0(k4_xboole_0(B_535, A_534), k3_xboole_0(k2_xboole_0(A_534, B_535), B_536)))=k4_xboole_0(k2_xboole_0(A_534, B_535), B_536))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11456])).
% 39.33/30.56  tff(c_69088, plain, (![B_180, A_179]: (k5_xboole_0(B_180, k4_xboole_0(A_179, k4_xboole_0(B_180, k2_xboole_0(B_180, A_179))))=k4_xboole_0(k2_xboole_0(B_180, A_179), k3_xboole_0(A_179, B_180)))), inference(superposition, [status(thm), theory('equality')], [c_8105, c_68947])).
% 39.33/30.56  tff(c_96836, plain, (![B_641, A_642]: (k4_xboole_0(k2_xboole_0(B_641, A_642), k3_xboole_0(A_642, B_641))=k5_xboole_0(B_641, A_642))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_69088])).
% 39.33/30.56  tff(c_97448, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), k3_xboole_0(B_2, A_1))=k5_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96836])).
% 39.33/30.56  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 39.33/30.56  tff(c_136334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97448, c_20])).
% 39.33/30.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.33/30.56  
% 39.33/30.56  Inference rules
% 39.33/30.56  ----------------------
% 39.33/30.56  #Ref     : 0
% 39.33/30.56  #Sup     : 34258
% 39.33/30.56  #Fact    : 0
% 39.33/30.56  #Define  : 0
% 39.33/30.56  #Split   : 0
% 39.33/30.56  #Chain   : 0
% 39.33/30.56  #Close   : 0
% 39.33/30.56  
% 39.33/30.56  Ordering : KBO
% 39.33/30.56  
% 39.33/30.56  Simplification rules
% 39.33/30.56  ----------------------
% 39.33/30.56  #Subsume      : 560
% 39.33/30.56  #Demod        : 53342
% 39.33/30.56  #Tautology    : 18128
% 39.33/30.56  #SimpNegUnit  : 0
% 39.33/30.56  #BackRed      : 24
% 39.33/30.56  
% 39.33/30.56  #Partial instantiations: 0
% 39.33/30.56  #Strategies tried      : 1
% 39.33/30.56  
% 39.33/30.56  Timing (in seconds)
% 39.33/30.56  ----------------------
% 39.33/30.56  Preprocessing        : 0.28
% 39.33/30.56  Parsing              : 0.15
% 39.33/30.56  CNF conversion       : 0.01
% 39.33/30.56  Main loop            : 29.52
% 39.33/30.56  Inferencing          : 2.74
% 39.33/30.56  Reduction            : 21.42
% 39.33/30.56  Demodulation         : 20.49
% 39.33/30.56  BG Simplification    : 0.46
% 39.33/30.56  Subsumption          : 4.03
% 39.33/30.56  Abstraction          : 0.93
% 39.47/30.56  MUC search           : 0.00
% 39.47/30.56  Cooper               : 0.00
% 39.47/30.56  Total                : 29.82
% 39.47/30.56  Index Insertion      : 0.00
% 39.47/30.56  Index Deletion       : 0.00
% 39.47/30.56  Index Matching       : 0.00
% 39.47/30.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
