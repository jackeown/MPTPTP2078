%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:24 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   25 (  31 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_xboole_0(k1_tarski(A_43),k1_enumset1(B_44,C_45,D_46)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_43,A_21,B_22] : k2_xboole_0(k1_tarski(A_43),k2_tarski(A_21,B_22)) = k2_enumset1(A_43,A_21,A_21,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_68,plain,(
    ! [A_43,A_21,B_22] : k2_enumset1(A_43,A_21,A_21,B_22) = k1_enumset1(A_43,A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_14,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k2_tarski(D_19,E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [D_61,A_63,C_64,E_60,B_65,F_62] : k2_xboole_0(k1_enumset1(A_63,B_65,C_64),k1_enumset1(D_61,E_60,F_62)) = k4_enumset1(A_63,B_65,C_64,D_61,E_60,F_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_21,B_22,A_63,C_64,B_65] : k4_enumset1(A_63,B_65,C_64,A_21,A_21,B_22) = k2_xboole_0(k1_enumset1(A_63,B_65,C_64),k2_tarski(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_100])).

tff(c_126,plain,(
    ! [B_70,A_74,B_73,A_72,C_71] : k4_enumset1(A_74,B_70,C_71,A_72,A_72,B_73) = k3_enumset1(A_74,B_70,C_71,A_72,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_enumset1(A_27,A_27,B_28,C_29,D_30,E_31) = k3_enumset1(A_27,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [B_70,C_71,A_72,B_73] : k3_enumset1(B_70,C_71,A_72,A_72,B_73) = k3_enumset1(B_70,B_70,C_71,A_72,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_16])).

tff(c_145,plain,(
    ! [B_75,C_76,A_77,B_78] : k3_enumset1(B_75,C_76,A_77,A_77,B_78) = k2_enumset1(B_75,C_76,A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_152,plain,(
    ! [C_76,A_77,B_78] : k2_enumset1(C_76,C_76,A_77,B_78) = k2_enumset1(C_76,A_77,A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_14])).

tff(c_161,plain,(
    ! [C_76,A_77,B_78] : k2_enumset1(C_76,C_76,A_77,B_78) = k1_enumset1(C_76,A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_152])).

tff(c_18,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.18  
% 1.90/1.20  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.90/1.20  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.90/1.20  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.90/1.20  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.90/1.20  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_enumset1)).
% 1.90/1.20  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 1.90/1.20  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.90/1.20  tff(f_44, negated_conjecture, ~(![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 1.90/1.20  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k1_tarski(A_9), k2_tarski(B_10, C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.20  tff(c_12, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.20  tff(c_56, plain, (![A_43, B_44, C_45, D_46]: (k2_xboole_0(k1_tarski(A_43), k1_enumset1(B_44, C_45, D_46))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.20  tff(c_65, plain, (![A_43, A_21, B_22]: (k2_xboole_0(k1_tarski(A_43), k2_tarski(A_21, B_22))=k2_enumset1(A_43, A_21, A_21, B_22))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56])).
% 1.90/1.20  tff(c_68, plain, (![A_43, A_21, B_22]: (k2_enumset1(A_43, A_21, A_21, B_22)=k1_enumset1(A_43, A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_65])).
% 1.90/1.20  tff(c_14, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.20  tff(c_10, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k2_tarski(D_19, E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.20  tff(c_100, plain, (![D_61, A_63, C_64, E_60, B_65, F_62]: (k2_xboole_0(k1_enumset1(A_63, B_65, C_64), k1_enumset1(D_61, E_60, F_62))=k4_enumset1(A_63, B_65, C_64, D_61, E_60, F_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.20  tff(c_112, plain, (![A_21, B_22, A_63, C_64, B_65]: (k4_enumset1(A_63, B_65, C_64, A_21, A_21, B_22)=k2_xboole_0(k1_enumset1(A_63, B_65, C_64), k2_tarski(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_100])).
% 1.90/1.20  tff(c_126, plain, (![B_70, A_74, B_73, A_72, C_71]: (k4_enumset1(A_74, B_70, C_71, A_72, A_72, B_73)=k3_enumset1(A_74, B_70, C_71, A_72, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_112])).
% 1.90/1.20  tff(c_16, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_enumset1(A_27, A_27, B_28, C_29, D_30, E_31)=k3_enumset1(A_27, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.20  tff(c_133, plain, (![B_70, C_71, A_72, B_73]: (k3_enumset1(B_70, C_71, A_72, A_72, B_73)=k3_enumset1(B_70, B_70, C_71, A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_126, c_16])).
% 1.90/1.20  tff(c_145, plain, (![B_75, C_76, A_77, B_78]: (k3_enumset1(B_75, C_76, A_77, A_77, B_78)=k2_enumset1(B_75, C_76, A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 1.90/1.20  tff(c_152, plain, (![C_76, A_77, B_78]: (k2_enumset1(C_76, C_76, A_77, B_78)=k2_enumset1(C_76, A_77, A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_145, c_14])).
% 1.90/1.20  tff(c_161, plain, (![C_76, A_77, B_78]: (k2_enumset1(C_76, C_76, A_77, B_78)=k1_enumset1(C_76, A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_152])).
% 1.90/1.20  tff(c_18, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.20  tff(c_19, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 1.90/1.20  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_19])).
% 1.90/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  Inference rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Ref     : 0
% 1.90/1.20  #Sup     : 32
% 1.90/1.20  #Fact    : 0
% 1.90/1.20  #Define  : 0
% 1.90/1.20  #Split   : 0
% 1.90/1.20  #Chain   : 0
% 1.90/1.20  #Close   : 0
% 1.90/1.20  
% 1.90/1.20  Ordering : KBO
% 1.90/1.20  
% 1.90/1.20  Simplification rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Subsume      : 0
% 1.90/1.20  #Demod        : 10
% 1.90/1.20  #Tautology    : 24
% 1.90/1.20  #SimpNegUnit  : 0
% 1.90/1.20  #BackRed      : 1
% 1.90/1.20  
% 1.90/1.20  #Partial instantiations: 0
% 1.90/1.20  #Strategies tried      : 1
% 1.90/1.20  
% 1.90/1.20  Timing (in seconds)
% 1.90/1.20  ----------------------
% 1.90/1.20  Preprocessing        : 0.29
% 1.90/1.20  Parsing              : 0.15
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.13
% 1.90/1.20  Inferencing          : 0.06
% 1.90/1.20  Reduction            : 0.04
% 1.90/1.20  Demodulation         : 0.03
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.01
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.45
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
