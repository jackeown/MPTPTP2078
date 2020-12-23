%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:13 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   33 (  53 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_tarski(A_3,B_4),k1_tarski(C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(C_47)) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_37,C_47] : k2_xboole_0(k1_tarski(A_37),k1_tarski(C_47)) = k1_enumset1(A_37,A_37,C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_62,plain,(
    ! [A_37,C_47] : k2_xboole_0(k1_tarski(A_37),k1_tarski(C_47)) = k2_tarski(A_37,C_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_63,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_xboole_0(k1_tarski(A_48),k1_enumset1(B_49,C_50,D_51)) = k2_enumset1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_54,A_55,B_56] : k2_xboole_0(k1_tarski(A_54),k2_tarski(A_55,B_56)) = k2_enumset1(A_54,A_55,A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_63])).

tff(c_99,plain,(
    ! [A_54,A_37] : k2_xboole_0(k1_tarski(A_54),k1_tarski(A_37)) = k2_enumset1(A_54,A_37,A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_84])).

tff(c_104,plain,(
    ! [A_54,A_37] : k2_enumset1(A_54,A_37,A_37,A_37) = k2_tarski(A_54,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_99])).

tff(c_123,plain,(
    ! [E_62,D_61,A_63,B_60,C_59] : k2_xboole_0(k2_enumset1(A_63,B_60,C_59,D_61),k1_tarski(E_62)) = k3_enumset1(A_63,B_60,C_59,D_61,E_62) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [A_54,A_37,E_62] : k3_enumset1(A_54,A_37,A_37,A_37,E_62) = k2_xboole_0(k2_tarski(A_54,A_37),k1_tarski(E_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_123])).

tff(c_138,plain,(
    ! [A_54,A_37,E_62] : k3_enumset1(A_54,A_37,A_37,A_37,E_62) = k1_enumset1(A_54,A_37,E_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_132])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [E_80,A_81,D_78,B_79,C_77] : k2_xboole_0(k2_tarski(A_81,B_79),k1_enumset1(C_77,D_78,E_80)) = k3_enumset1(A_81,B_79,C_77,D_78,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_37,C_77,D_78,E_80] : k3_enumset1(A_37,A_37,C_77,D_78,E_80) = k2_xboole_0(k1_tarski(A_37),k1_enumset1(C_77,D_78,E_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_223])).

tff(c_269,plain,(
    ! [A_84,C_85,D_86,E_87] : k3_enumset1(A_84,A_84,C_85,D_86,E_87) = k2_enumset1(A_84,C_85,D_86,E_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_238])).

tff(c_299,plain,(
    ! [A_37,E_62] : k2_enumset1(A_37,A_37,A_37,E_62) = k1_enumset1(A_37,A_37,E_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_269])).

tff(c_367,plain,(
    ! [A_95,E_96] : k2_enumset1(A_95,A_95,A_95,E_96) = k2_tarski(A_95,E_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_299])).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] : k2_xboole_0(k2_enumset1(A_20,B_21,C_22,D_23),k1_tarski(E_24)) = k3_enumset1(A_20,B_21,C_22,D_23,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_380,plain,(
    ! [A_95,E_96,E_24] : k3_enumset1(A_95,A_95,A_95,E_96,E_24) = k2_xboole_0(k2_tarski(A_95,E_96),k1_tarski(E_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_12])).

tff(c_1294,plain,(
    ! [A_143,E_144,E_145] : k3_enumset1(A_143,A_143,A_143,E_144,E_145) = k1_enumset1(A_143,E_144,E_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_380])).

tff(c_241,plain,(
    ! [A_37,C_77,D_78,E_80] : k3_enumset1(A_37,A_37,C_77,D_78,E_80) = k2_enumset1(A_37,C_77,D_78,E_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_238])).

tff(c_1326,plain,(
    ! [A_143,E_144,E_145] : k2_enumset1(A_143,A_143,E_144,E_145) = k1_enumset1(A_143,E_144,E_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_241])).

tff(c_22,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.46  
% 2.73/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.47  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.73/1.47  
% 2.73/1.47  %Foreground sorts:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Background operators:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Foreground operators:
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.47  
% 3.11/1.48  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.11/1.48  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.11/1.48  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.11/1.48  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.11/1.48  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.11/1.48  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 3.11/1.48  tff(f_48, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.11/1.48  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_tarski(A_3, B_4), k1_tarski(C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.11/1.48  tff(c_20, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.48  tff(c_18, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.48  tff(c_50, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(C_47))=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.11/1.48  tff(c_59, plain, (![A_37, C_47]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(C_47))=k1_enumset1(A_37, A_37, C_47))), inference(superposition, [status(thm), theory('equality')], [c_18, c_50])).
% 3.11/1.48  tff(c_62, plain, (![A_37, C_47]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(C_47))=k2_tarski(A_37, C_47))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 3.11/1.48  tff(c_63, plain, (![A_48, B_49, C_50, D_51]: (k2_xboole_0(k1_tarski(A_48), k1_enumset1(B_49, C_50, D_51))=k2_enumset1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.48  tff(c_84, plain, (![A_54, A_55, B_56]: (k2_xboole_0(k1_tarski(A_54), k2_tarski(A_55, B_56))=k2_enumset1(A_54, A_55, A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_20, c_63])).
% 3.11/1.48  tff(c_99, plain, (![A_54, A_37]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(A_37))=k2_enumset1(A_54, A_37, A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_18, c_84])).
% 3.11/1.48  tff(c_104, plain, (![A_54, A_37]: (k2_enumset1(A_54, A_37, A_37, A_37)=k2_tarski(A_54, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_99])).
% 3.11/1.48  tff(c_123, plain, (![E_62, D_61, A_63, B_60, C_59]: (k2_xboole_0(k2_enumset1(A_63, B_60, C_59, D_61), k1_tarski(E_62))=k3_enumset1(A_63, B_60, C_59, D_61, E_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.11/1.48  tff(c_132, plain, (![A_54, A_37, E_62]: (k3_enumset1(A_54, A_37, A_37, A_37, E_62)=k2_xboole_0(k2_tarski(A_54, A_37), k1_tarski(E_62)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_123])).
% 3.11/1.48  tff(c_138, plain, (![A_54, A_37, E_62]: (k3_enumset1(A_54, A_37, A_37, A_37, E_62)=k1_enumset1(A_54, A_37, E_62))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_132])).
% 3.11/1.48  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.48  tff(c_223, plain, (![E_80, A_81, D_78, B_79, C_77]: (k2_xboole_0(k2_tarski(A_81, B_79), k1_enumset1(C_77, D_78, E_80))=k3_enumset1(A_81, B_79, C_77, D_78, E_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.48  tff(c_238, plain, (![A_37, C_77, D_78, E_80]: (k3_enumset1(A_37, A_37, C_77, D_78, E_80)=k2_xboole_0(k1_tarski(A_37), k1_enumset1(C_77, D_78, E_80)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_223])).
% 3.11/1.48  tff(c_269, plain, (![A_84, C_85, D_86, E_87]: (k3_enumset1(A_84, A_84, C_85, D_86, E_87)=k2_enumset1(A_84, C_85, D_86, E_87))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_238])).
% 3.11/1.48  tff(c_299, plain, (![A_37, E_62]: (k2_enumset1(A_37, A_37, A_37, E_62)=k1_enumset1(A_37, A_37, E_62))), inference(superposition, [status(thm), theory('equality')], [c_138, c_269])).
% 3.11/1.48  tff(c_367, plain, (![A_95, E_96]: (k2_enumset1(A_95, A_95, A_95, E_96)=k2_tarski(A_95, E_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_299])).
% 3.11/1.48  tff(c_12, plain, (![C_22, D_23, A_20, B_21, E_24]: (k2_xboole_0(k2_enumset1(A_20, B_21, C_22, D_23), k1_tarski(E_24))=k3_enumset1(A_20, B_21, C_22, D_23, E_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.11/1.48  tff(c_380, plain, (![A_95, E_96, E_24]: (k3_enumset1(A_95, A_95, A_95, E_96, E_24)=k2_xboole_0(k2_tarski(A_95, E_96), k1_tarski(E_24)))), inference(superposition, [status(thm), theory('equality')], [c_367, c_12])).
% 3.11/1.48  tff(c_1294, plain, (![A_143, E_144, E_145]: (k3_enumset1(A_143, A_143, A_143, E_144, E_145)=k1_enumset1(A_143, E_144, E_145))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_380])).
% 3.11/1.48  tff(c_241, plain, (![A_37, C_77, D_78, E_80]: (k3_enumset1(A_37, A_37, C_77, D_78, E_80)=k2_enumset1(A_37, C_77, D_78, E_80))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_238])).
% 3.11/1.48  tff(c_1326, plain, (![A_143, E_144, E_145]: (k2_enumset1(A_143, A_143, E_144, E_145)=k1_enumset1(A_143, E_144, E_145))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_241])).
% 3.11/1.48  tff(c_22, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.48  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1326, c_22])).
% 3.11/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.48  
% 3.11/1.48  Inference rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Ref     : 0
% 3.11/1.48  #Sup     : 332
% 3.11/1.48  #Fact    : 0
% 3.11/1.48  #Define  : 0
% 3.11/1.48  #Split   : 0
% 3.11/1.48  #Chain   : 0
% 3.11/1.48  #Close   : 0
% 3.11/1.48  
% 3.11/1.48  Ordering : KBO
% 3.11/1.48  
% 3.11/1.48  Simplification rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Subsume      : 4
% 3.11/1.48  #Demod        : 364
% 3.11/1.48  #Tautology    : 259
% 3.11/1.48  #SimpNegUnit  : 0
% 3.11/1.48  #BackRed      : 5
% 3.11/1.48  
% 3.11/1.48  #Partial instantiations: 0
% 3.11/1.48  #Strategies tried      : 1
% 3.11/1.48  
% 3.11/1.48  Timing (in seconds)
% 3.11/1.48  ----------------------
% 3.11/1.48  Preprocessing        : 0.32
% 3.11/1.48  Parsing              : 0.17
% 3.11/1.48  CNF conversion       : 0.02
% 3.11/1.48  Main loop            : 0.41
% 3.11/1.48  Inferencing          : 0.18
% 3.11/1.48  Reduction            : 0.16
% 3.11/1.48  Demodulation         : 0.12
% 3.11/1.48  BG Simplification    : 0.02
% 3.11/1.48  Subsumption          : 0.04
% 3.11/1.48  Abstraction          : 0.03
% 3.11/1.48  MUC search           : 0.00
% 3.11/1.48  Cooper               : 0.00
% 3.11/1.48  Total                : 0.76
% 3.11/1.48  Index Insertion      : 0.00
% 3.11/1.48  Index Deletion       : 0.00
% 3.11/1.48  Index Matching       : 0.00
% 3.11/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
