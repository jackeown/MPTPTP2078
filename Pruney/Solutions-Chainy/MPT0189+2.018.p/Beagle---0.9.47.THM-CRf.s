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
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  54 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_6,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_43,B_44,C_45,D_46] : k3_enumset1(A_43,A_43,B_44,C_45,D_46) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_590,plain,(
    ! [E_104,B_103,A_105,C_106,D_102] : k2_xboole_0(k2_tarski(A_105,B_103),k1_enumset1(C_106,D_102,E_104)) = k3_enumset1(A_105,B_103,C_106,D_102,E_104) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_623,plain,(
    ! [A_37,C_106,D_102,E_104] : k3_enumset1(A_37,A_37,C_106,D_102,E_104) = k2_xboole_0(k1_tarski(A_37),k1_enumset1(C_106,D_102,E_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_590])).

tff(c_626,plain,(
    ! [A_37,C_106,D_102,E_104] : k2_xboole_0(k1_tarski(A_37),k1_enumset1(C_106,D_102,E_104)) = k2_enumset1(A_37,C_106,D_102,E_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_623])).

tff(c_22,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_630,plain,(
    ! [B_111,C_108,A_107,E_109,D_110] : k2_xboole_0(k2_enumset1(A_107,B_111,C_108,D_110),k1_tarski(E_109)) = k3_enumset1(A_107,B_111,C_108,D_110,E_109) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2840,plain,(
    ! [C_195,E_198,A_197,B_196,D_194] : k2_xboole_0(k1_tarski(E_198),k2_enumset1(A_197,B_196,C_195,D_194)) = k3_enumset1(A_197,B_196,C_195,D_194,E_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_2])).

tff(c_2915,plain,(
    ! [A_40,B_41,C_42,E_198] : k3_enumset1(A_40,A_40,B_41,C_42,E_198) = k2_xboole_0(k1_tarski(E_198),k1_enumset1(A_40,B_41,C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2840])).

tff(c_2931,plain,(
    ! [E_198,A_40,B_41,C_42] : k2_enumset1(E_198,A_40,B_41,C_42) = k2_enumset1(A_40,B_41,C_42,E_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_24,c_2915])).

tff(c_30,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_30])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_3547,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2931,c_2931,c_32])).

tff(c_3550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_3547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.76  
% 4.24/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.76  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.24/1.76  
% 4.24/1.76  %Foreground sorts:
% 4.24/1.76  
% 4.24/1.76  
% 4.24/1.76  %Background operators:
% 4.24/1.76  
% 4.24/1.76  
% 4.24/1.76  %Foreground operators:
% 4.24/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.24/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.24/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.24/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.24/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.24/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.24/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.24/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.24/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.24/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.24/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.24/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.24/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.24/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.24/1.76  
% 4.24/1.77  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 4.24/1.77  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 4.24/1.77  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.24/1.77  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.24/1.77  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 4.24/1.77  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.24/1.77  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 4.24/1.77  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.24/1.77  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.24/1.77  tff(c_6, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.77  tff(c_8, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.24/1.77  tff(c_24, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.24/1.77  tff(c_18, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.24/1.77  tff(c_590, plain, (![E_104, B_103, A_105, C_106, D_102]: (k2_xboole_0(k2_tarski(A_105, B_103), k1_enumset1(C_106, D_102, E_104))=k3_enumset1(A_105, B_103, C_106, D_102, E_104))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.24/1.77  tff(c_623, plain, (![A_37, C_106, D_102, E_104]: (k3_enumset1(A_37, A_37, C_106, D_102, E_104)=k2_xboole_0(k1_tarski(A_37), k1_enumset1(C_106, D_102, E_104)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_590])).
% 4.24/1.77  tff(c_626, plain, (![A_37, C_106, D_102, E_104]: (k2_xboole_0(k1_tarski(A_37), k1_enumset1(C_106, D_102, E_104))=k2_enumset1(A_37, C_106, D_102, E_104))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_623])).
% 4.24/1.77  tff(c_22, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.24/1.77  tff(c_630, plain, (![B_111, C_108, A_107, E_109, D_110]: (k2_xboole_0(k2_enumset1(A_107, B_111, C_108, D_110), k1_tarski(E_109))=k3_enumset1(A_107, B_111, C_108, D_110, E_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.24/1.77  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.24/1.77  tff(c_2840, plain, (![C_195, E_198, A_197, B_196, D_194]: (k2_xboole_0(k1_tarski(E_198), k2_enumset1(A_197, B_196, C_195, D_194))=k3_enumset1(A_197, B_196, C_195, D_194, E_198))), inference(superposition, [status(thm), theory('equality')], [c_630, c_2])).
% 4.24/1.77  tff(c_2915, plain, (![A_40, B_41, C_42, E_198]: (k3_enumset1(A_40, A_40, B_41, C_42, E_198)=k2_xboole_0(k1_tarski(E_198), k1_enumset1(A_40, B_41, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2840])).
% 4.24/1.77  tff(c_2931, plain, (![E_198, A_40, B_41, C_42]: (k2_enumset1(E_198, A_40, B_41, C_42)=k2_enumset1(A_40, B_41, C_42, E_198))), inference(demodulation, [status(thm), theory('equality')], [c_626, c_24, c_2915])).
% 4.24/1.77  tff(c_30, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.24/1.77  tff(c_31, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_30])).
% 4.24/1.77  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_31])).
% 4.24/1.77  tff(c_3547, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2931, c_2931, c_32])).
% 4.24/1.77  tff(c_3550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_3547])).
% 4.24/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.24/1.77  
% 4.24/1.77  Inference rules
% 4.24/1.77  ----------------------
% 4.24/1.77  #Ref     : 0
% 4.24/1.77  #Sup     : 857
% 4.24/1.77  #Fact    : 0
% 4.24/1.77  #Define  : 0
% 4.24/1.77  #Split   : 0
% 4.24/1.77  #Chain   : 0
% 4.24/1.77  #Close   : 0
% 4.24/1.77  
% 4.24/1.77  Ordering : KBO
% 4.24/1.77  
% 4.24/1.77  Simplification rules
% 4.24/1.77  ----------------------
% 4.24/1.77  #Subsume      : 72
% 4.24/1.77  #Demod        : 639
% 4.24/1.77  #Tautology    : 553
% 4.24/1.77  #SimpNegUnit  : 0
% 4.24/1.77  #BackRed      : 1
% 4.24/1.77  
% 4.24/1.77  #Partial instantiations: 0
% 4.24/1.77  #Strategies tried      : 1
% 4.24/1.77  
% 4.24/1.77  Timing (in seconds)
% 4.24/1.77  ----------------------
% 4.58/1.77  Preprocessing        : 0.30
% 4.58/1.77  Parsing              : 0.16
% 4.58/1.78  CNF conversion       : 0.02
% 4.58/1.78  Main loop            : 0.73
% 4.58/1.78  Inferencing          : 0.24
% 4.58/1.78  Reduction            : 0.34
% 4.58/1.78  Demodulation         : 0.30
% 4.58/1.78  BG Simplification    : 0.03
% 4.58/1.78  Subsumption          : 0.09
% 4.58/1.78  Abstraction          : 0.04
% 4.58/1.78  MUC search           : 0.00
% 4.58/1.78  Cooper               : 0.00
% 4.58/1.78  Total                : 1.06
% 4.58/1.78  Index Insertion      : 0.00
% 4.58/1.78  Index Deletion       : 0.00
% 4.58/1.78  Index Matching       : 0.00
% 4.58/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
