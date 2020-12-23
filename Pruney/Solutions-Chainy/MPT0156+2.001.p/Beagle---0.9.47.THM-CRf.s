%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 6.81s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   39 (  65 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_16,plain,(
    ! [A_13,B_14,C_15,D_16] : k2_xboole_0(k2_tarski(A_13,B_14),k2_tarski(C_15,D_16)) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_210,plain,(
    ! [A_58,B_59,C_60,D_61] : k2_xboole_0(k2_tarski(A_58,B_59),k2_tarski(C_60,D_61)) = k2_enumset1(A_58,B_59,C_60,D_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_222,plain,(
    ! [A_58,B_59,C_60,D_61] : k2_xboole_0(k2_tarski(A_58,B_59),k2_enumset1(A_58,B_59,C_60,D_61)) = k2_xboole_0(k2_tarski(A_58,B_59),k2_tarski(C_60,D_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_46])).

tff(c_251,plain,(
    ! [A_58,B_59,C_60,D_61] : k2_xboole_0(k2_tarski(A_58,B_59),k2_enumset1(A_58,B_59,C_60,D_61)) = k2_enumset1(A_58,B_59,C_60,D_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_222])).

tff(c_18,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k2_xboole_0(k1_tarski(A_17),k2_enumset1(B_18,C_19,D_20,E_21)) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_328,plain,(
    ! [A_70,B_71,C_72,D_73] : r1_tarski(k2_tarski(A_70,B_71),k2_enumset1(A_70,B_71,C_72,D_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_14])).

tff(c_341,plain,(
    ! [A_25,B_26,C_27] : r1_tarski(k2_tarski(A_25,A_25),k1_enumset1(A_25,B_26,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_328])).

tff(c_351,plain,(
    ! [A_74,B_75,C_76] : r1_tarski(k1_tarski(A_74),k1_enumset1(A_74,B_75,C_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_341])).

tff(c_369,plain,(
    ! [A_77,B_78] : r1_tarski(k1_tarski(A_77),k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_351])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_446,plain,(
    ! [A_88,B_89] : k2_xboole_0(k1_tarski(A_88),k2_tarski(A_88,B_89)) = k2_tarski(A_88,B_89) ),
    inference(resolution,[status(thm)],[c_369,c_10])).

tff(c_80,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_39,B_41,B_12] : r1_tarski(A_39,k2_xboole_0(k2_xboole_0(A_39,B_41),B_12)) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_483,plain,(
    ! [A_90,B_91,B_92] : r1_tarski(k1_tarski(A_90),k2_xboole_0(k2_tarski(A_90,B_91),B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_92])).

tff(c_7705,plain,(
    ! [A_451,B_452,B_453] : k2_xboole_0(k1_tarski(A_451),k2_xboole_0(k2_tarski(A_451,B_452),B_453)) = k2_xboole_0(k2_tarski(A_451,B_452),B_453) ),
    inference(resolution,[status(thm)],[c_483,c_10])).

tff(c_7789,plain,(
    ! [A_58,B_59,C_60,D_61] : k2_xboole_0(k2_tarski(A_58,B_59),k2_enumset1(A_58,B_59,C_60,D_61)) = k2_xboole_0(k1_tarski(A_58),k2_enumset1(A_58,B_59,C_60,D_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_7705])).

tff(c_7834,plain,(
    ! [A_58,B_59,C_60,D_61] : k3_enumset1(A_58,A_58,B_59,C_60,D_61) = k2_enumset1(A_58,B_59,C_60,D_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_18,c_7789])).

tff(c_26,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7834,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.81/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.63  
% 6.81/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.63  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.81/2.63  
% 6.81/2.63  %Foreground sorts:
% 6.81/2.63  
% 6.81/2.63  
% 6.81/2.63  %Background operators:
% 6.81/2.63  
% 6.81/2.63  
% 6.81/2.63  %Foreground operators:
% 6.81/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.81/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.81/2.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.81/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.81/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.81/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.81/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.81/2.63  tff('#skF_2', type, '#skF_2': $i).
% 6.81/2.63  tff('#skF_3', type, '#skF_3': $i).
% 6.81/2.63  tff('#skF_1', type, '#skF_1': $i).
% 6.81/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.81/2.63  tff('#skF_4', type, '#skF_4': $i).
% 6.81/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.81/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.81/2.63  
% 6.81/2.64  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 6.81/2.64  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.81/2.64  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.81/2.64  tff(f_51, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 6.81/2.64  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.81/2.64  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.81/2.64  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.81/2.64  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.81/2.64  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.81/2.64  tff(c_16, plain, (![A_13, B_14, C_15, D_16]: (k2_xboole_0(k2_tarski(A_13, B_14), k2_tarski(C_15, D_16))=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.81/2.64  tff(c_210, plain, (![A_58, B_59, C_60, D_61]: (k2_xboole_0(k2_tarski(A_58, B_59), k2_tarski(C_60, D_61))=k2_enumset1(A_58, B_59, C_60, D_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.81/2.64  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.81/2.64  tff(c_39, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.81/2.64  tff(c_46, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_39])).
% 6.81/2.64  tff(c_222, plain, (![A_58, B_59, C_60, D_61]: (k2_xboole_0(k2_tarski(A_58, B_59), k2_enumset1(A_58, B_59, C_60, D_61))=k2_xboole_0(k2_tarski(A_58, B_59), k2_tarski(C_60, D_61)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_46])).
% 6.81/2.64  tff(c_251, plain, (![A_58, B_59, C_60, D_61]: (k2_xboole_0(k2_tarski(A_58, B_59), k2_enumset1(A_58, B_59, C_60, D_61))=k2_enumset1(A_58, B_59, C_60, D_61))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_222])).
% 6.81/2.64  tff(c_18, plain, (![E_21, D_20, C_19, B_18, A_17]: (k2_xboole_0(k1_tarski(A_17), k2_enumset1(B_18, C_19, D_20, E_21))=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.81/2.64  tff(c_22, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.81/2.64  tff(c_20, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.81/2.64  tff(c_24, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.81/2.64  tff(c_328, plain, (![A_70, B_71, C_72, D_73]: (r1_tarski(k2_tarski(A_70, B_71), k2_enumset1(A_70, B_71, C_72, D_73)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_14])).
% 6.81/2.64  tff(c_341, plain, (![A_25, B_26, C_27]: (r1_tarski(k2_tarski(A_25, A_25), k1_enumset1(A_25, B_26, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_328])).
% 6.81/2.64  tff(c_351, plain, (![A_74, B_75, C_76]: (r1_tarski(k1_tarski(A_74), k1_enumset1(A_74, B_75, C_76)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_341])).
% 6.81/2.64  tff(c_369, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_351])).
% 6.81/2.64  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.81/2.64  tff(c_446, plain, (![A_88, B_89]: (k2_xboole_0(k1_tarski(A_88), k2_tarski(A_88, B_89))=k2_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_369, c_10])).
% 6.81/2.64  tff(c_80, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.81/2.64  tff(c_92, plain, (![A_39, B_41, B_12]: (r1_tarski(A_39, k2_xboole_0(k2_xboole_0(A_39, B_41), B_12)))), inference(resolution, [status(thm)], [c_14, c_80])).
% 6.81/2.64  tff(c_483, plain, (![A_90, B_91, B_92]: (r1_tarski(k1_tarski(A_90), k2_xboole_0(k2_tarski(A_90, B_91), B_92)))), inference(superposition, [status(thm), theory('equality')], [c_446, c_92])).
% 6.81/2.64  tff(c_7705, plain, (![A_451, B_452, B_453]: (k2_xboole_0(k1_tarski(A_451), k2_xboole_0(k2_tarski(A_451, B_452), B_453))=k2_xboole_0(k2_tarski(A_451, B_452), B_453))), inference(resolution, [status(thm)], [c_483, c_10])).
% 6.81/2.64  tff(c_7789, plain, (![A_58, B_59, C_60, D_61]: (k2_xboole_0(k2_tarski(A_58, B_59), k2_enumset1(A_58, B_59, C_60, D_61))=k2_xboole_0(k1_tarski(A_58), k2_enumset1(A_58, B_59, C_60, D_61)))), inference(superposition, [status(thm), theory('equality')], [c_251, c_7705])).
% 6.81/2.64  tff(c_7834, plain, (![A_58, B_59, C_60, D_61]: (k3_enumset1(A_58, A_58, B_59, C_60, D_61)=k2_enumset1(A_58, B_59, C_60, D_61))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_18, c_7789])).
% 6.81/2.64  tff(c_26, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.81/2.64  tff(c_7845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7834, c_26])).
% 6.81/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.64  
% 6.81/2.64  Inference rules
% 6.81/2.64  ----------------------
% 6.81/2.64  #Ref     : 0
% 6.81/2.64  #Sup     : 2050
% 6.81/2.64  #Fact    : 0
% 6.81/2.64  #Define  : 0
% 6.81/2.64  #Split   : 0
% 6.81/2.64  #Chain   : 0
% 6.81/2.64  #Close   : 0
% 6.81/2.64  
% 6.81/2.64  Ordering : KBO
% 6.81/2.64  
% 6.81/2.64  Simplification rules
% 6.81/2.64  ----------------------
% 6.81/2.64  #Subsume      : 296
% 6.81/2.64  #Demod        : 859
% 6.81/2.64  #Tautology    : 576
% 6.81/2.64  #SimpNegUnit  : 0
% 6.81/2.64  #BackRed      : 1
% 6.81/2.64  
% 6.81/2.64  #Partial instantiations: 0
% 6.81/2.64  #Strategies tried      : 1
% 6.81/2.64  
% 6.81/2.64  Timing (in seconds)
% 6.81/2.64  ----------------------
% 6.81/2.64  Preprocessing        : 0.28
% 6.81/2.64  Parsing              : 0.15
% 6.81/2.64  CNF conversion       : 0.02
% 6.81/2.64  Main loop            : 1.49
% 6.81/2.64  Inferencing          : 0.43
% 6.81/2.64  Reduction            : 0.58
% 6.81/2.64  Demodulation         : 0.48
% 6.81/2.64  BG Simplification    : 0.05
% 6.81/2.64  Subsumption          : 0.33
% 6.81/2.64  Abstraction          : 0.07
% 6.81/2.64  MUC search           : 0.00
% 6.81/2.64  Cooper               : 0.00
% 6.81/2.64  Total                : 1.80
% 6.81/2.64  Index Insertion      : 0.00
% 6.81/2.64  Index Deletion       : 0.00
% 6.81/2.64  Index Matching       : 0.00
% 6.81/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
