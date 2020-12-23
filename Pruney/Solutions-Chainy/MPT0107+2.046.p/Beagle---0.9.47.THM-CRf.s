%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 105 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 ( 100 expanded)
%              Number of equality atoms :   39 (  87 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_315,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_324,plain,(
    ! [A_42,B_43] : k5_xboole_0(k4_xboole_0(A_42,B_43),k3_xboole_0(A_42,B_43)) = k2_xboole_0(k4_xboole_0(A_42,B_43),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_20])).

tff(c_1212,plain,(
    ! [A_73,B_74] : k5_xboole_0(k4_xboole_0(A_73,B_74),k3_xboole_0(A_73,B_74)) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_324])).

tff(c_1443,plain,(
    ! [A_79,B_80] : k5_xboole_0(k3_xboole_0(A_79,B_80),k4_xboole_0(A_79,B_80)) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1212])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_32,B_33] : k4_xboole_0(k2_xboole_0(A_32,B_33),B_33) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_xboole_0) = k2_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_10])).

tff(c_136,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_140,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_xboole_0) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_150,plain,(
    ! [B_7] : k4_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_85])).

tff(c_224,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k4_xboole_0(B_39,A_38)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_233,plain,(
    ! [B_7] : k5_xboole_0(B_7,k1_xboole_0) = k2_xboole_0(B_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_224])).

tff(c_244,plain,(
    ! [B_40] : k5_xboole_0(B_40,k1_xboole_0) = B_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_233])).

tff(c_250,plain,(
    ! [B_40] : k5_xboole_0(k1_xboole_0,B_40) = B_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_2])).

tff(c_242,plain,(
    ! [B_7] : k5_xboole_0(B_7,k1_xboole_0) = B_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_233])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_467,plain,(
    ! [A_48,B_49] : k5_xboole_0(k5_xboole_0(A_48,B_49),k2_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_500,plain,(
    ! [A_32] : k5_xboole_0(k5_xboole_0(A_32,k1_xboole_0),A_32) = k3_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_467])).

tff(c_524,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_6,c_500])).

tff(c_584,plain,(
    ! [A_52,B_53,C_54] : k5_xboole_0(k5_xboole_0(A_52,B_53),C_54) = k5_xboole_0(A_52,k5_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_624,plain,(
    ! [A_32,C_54] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_54)) = k5_xboole_0(k1_xboole_0,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_584])).

tff(c_671,plain,(
    ! [A_32,C_54] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_54)) = C_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_624])).

tff(c_2698,plain,(
    ! [A_102,B_103] : k5_xboole_0(k3_xboole_0(A_102,B_103),A_102) = k4_xboole_0(A_102,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_671])).

tff(c_2787,plain,(
    ! [A_1,B_103] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_103)) = k4_xboole_0(A_1,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2698])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.65  
% 3.62/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.65  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.62/1.65  
% 3.62/1.65  %Foreground sorts:
% 3.62/1.65  
% 3.62/1.65  
% 3.62/1.65  %Background operators:
% 3.62/1.65  
% 3.62/1.65  
% 3.62/1.65  %Foreground operators:
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.62/1.65  
% 3.86/1.66  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.86/1.66  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.86/1.66  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.86/1.66  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.86/1.66  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.86/1.66  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.86/1.66  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.86/1.66  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.86/1.66  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.86/1.66  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.86/1.66  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.86/1.66  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.86/1.66  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.86/1.66  tff(c_77, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.66  tff(c_85, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_8, c_77])).
% 3.86/1.66  tff(c_315, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.86/1.66  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.86/1.66  tff(c_324, plain, (![A_42, B_43]: (k5_xboole_0(k4_xboole_0(A_42, B_43), k3_xboole_0(A_42, B_43))=k2_xboole_0(k4_xboole_0(A_42, B_43), A_42))), inference(superposition, [status(thm), theory('equality')], [c_315, c_20])).
% 3.86/1.66  tff(c_1212, plain, (![A_73, B_74]: (k5_xboole_0(k4_xboole_0(A_73, B_74), k3_xboole_0(A_73, B_74))=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_324])).
% 3.86/1.66  tff(c_1443, plain, (![A_79, B_80]: (k5_xboole_0(k3_xboole_0(A_79, B_80), k4_xboole_0(A_79, B_80))=A_79)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1212])).
% 3.86/1.66  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.86/1.66  tff(c_108, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(A_32, B_33), B_33)=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.86/1.66  tff(c_121, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=k2_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_10])).
% 3.86/1.66  tff(c_136, plain, (![A_32]: (k2_xboole_0(A_32, k1_xboole_0)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_121])).
% 3.86/1.66  tff(c_140, plain, (![A_34]: (k2_xboole_0(A_34, k1_xboole_0)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_121])).
% 3.86/1.66  tff(c_150, plain, (![B_7]: (k4_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_85])).
% 3.86/1.66  tff(c_224, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k4_xboole_0(B_39, A_38))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.86/1.66  tff(c_233, plain, (![B_7]: (k5_xboole_0(B_7, k1_xboole_0)=k2_xboole_0(B_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_150, c_224])).
% 3.86/1.66  tff(c_244, plain, (![B_40]: (k5_xboole_0(B_40, k1_xboole_0)=B_40)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_233])).
% 3.86/1.66  tff(c_250, plain, (![B_40]: (k5_xboole_0(k1_xboole_0, B_40)=B_40)), inference(superposition, [status(thm), theory('equality')], [c_244, c_2])).
% 3.86/1.66  tff(c_242, plain, (![B_7]: (k5_xboole_0(B_7, k1_xboole_0)=B_7)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_233])).
% 3.86/1.66  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.86/1.66  tff(c_467, plain, (![A_48, B_49]: (k5_xboole_0(k5_xboole_0(A_48, B_49), k2_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.86/1.66  tff(c_500, plain, (![A_32]: (k5_xboole_0(k5_xboole_0(A_32, k1_xboole_0), A_32)=k3_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_467])).
% 3.86/1.66  tff(c_524, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_6, c_500])).
% 3.86/1.66  tff(c_584, plain, (![A_52, B_53, C_54]: (k5_xboole_0(k5_xboole_0(A_52, B_53), C_54)=k5_xboole_0(A_52, k5_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.86/1.66  tff(c_624, plain, (![A_32, C_54]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_54))=k5_xboole_0(k1_xboole_0, C_54))), inference(superposition, [status(thm), theory('equality')], [c_524, c_584])).
% 3.86/1.66  tff(c_671, plain, (![A_32, C_54]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_54))=C_54)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_624])).
% 3.86/1.66  tff(c_2698, plain, (![A_102, B_103]: (k5_xboole_0(k3_xboole_0(A_102, B_103), A_102)=k4_xboole_0(A_102, B_103))), inference(superposition, [status(thm), theory('equality')], [c_1443, c_671])).
% 3.86/1.66  tff(c_2787, plain, (![A_1, B_103]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_103))=k4_xboole_0(A_1, B_103))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2698])).
% 3.86/1.66  tff(c_22, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.66  tff(c_3340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2787, c_22])).
% 3.86/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.66  
% 3.86/1.66  Inference rules
% 3.86/1.66  ----------------------
% 3.86/1.66  #Ref     : 0
% 3.86/1.66  #Sup     : 833
% 3.86/1.66  #Fact    : 0
% 3.86/1.66  #Define  : 0
% 3.86/1.66  #Split   : 0
% 3.86/1.66  #Chain   : 0
% 3.86/1.66  #Close   : 0
% 3.86/1.66  
% 3.86/1.66  Ordering : KBO
% 3.86/1.66  
% 3.86/1.66  Simplification rules
% 3.86/1.66  ----------------------
% 3.86/1.66  #Subsume      : 20
% 3.86/1.66  #Demod        : 715
% 3.86/1.66  #Tautology    : 521
% 3.86/1.66  #SimpNegUnit  : 0
% 3.86/1.66  #BackRed      : 2
% 3.86/1.66  
% 3.86/1.66  #Partial instantiations: 0
% 3.86/1.66  #Strategies tried      : 1
% 3.86/1.66  
% 3.86/1.66  Timing (in seconds)
% 3.86/1.66  ----------------------
% 3.86/1.66  Preprocessing        : 0.27
% 3.86/1.66  Parsing              : 0.15
% 3.86/1.66  CNF conversion       : 0.01
% 3.86/1.66  Main loop            : 0.63
% 3.86/1.67  Inferencing          : 0.21
% 3.86/1.67  Reduction            : 0.28
% 3.86/1.67  Demodulation         : 0.24
% 3.86/1.67  BG Simplification    : 0.03
% 3.86/1.67  Subsumption          : 0.08
% 3.86/1.67  Abstraction          : 0.04
% 3.86/1.67  MUC search           : 0.00
% 3.86/1.67  Cooper               : 0.00
% 3.86/1.67  Total                : 0.93
% 3.86/1.67  Index Insertion      : 0.00
% 3.86/1.67  Index Deletion       : 0.00
% 3.86/1.67  Index Matching       : 0.00
% 3.86/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
