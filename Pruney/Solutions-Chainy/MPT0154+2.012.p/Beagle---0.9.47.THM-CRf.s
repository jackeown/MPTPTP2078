%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:05 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_48,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),k1_tarski(B_32)) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ! [A_49] : k2_tarski(A_49,A_49) = k1_tarski(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k1_tarski(A_33),k2_tarski(B_34,C_35)) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_654,plain,(
    ! [A_112,B_113,C_114,D_115] : k2_xboole_0(k2_tarski(A_112,B_113),k2_tarski(C_114,D_115)) = k2_enumset1(A_112,B_113,C_114,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_671,plain,(
    ! [A_49,C_114,D_115] : k2_xboole_0(k1_tarski(A_49),k2_tarski(C_114,D_115)) = k2_enumset1(A_49,A_49,C_114,D_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_654])).

tff(c_1673,plain,(
    ! [A_161,C_162,D_163] : k2_enumset1(A_161,A_161,C_162,D_163) = k1_enumset1(A_161,C_162,D_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_671])).

tff(c_38,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    ! [A_69] : k4_xboole_0(A_69,A_69) = k3_xboole_0(A_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_194])).

tff(c_44,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_561,plain,(
    ! [A_110] : k5_xboole_0(A_110,k3_xboole_0(A_110,k1_xboole_0)) = k2_xboole_0(A_110,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_582,plain,(
    ! [A_110] : k4_xboole_0(A_110,k1_xboole_0) = k2_xboole_0(A_110,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_34])).

tff(c_617,plain,(
    ! [A_110] : k2_xboole_0(A_110,A_110) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_582])).

tff(c_668,plain,(
    ! [A_112,B_113] : k2_enumset1(A_112,B_113,A_112,B_113) = k2_tarski(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_654])).

tff(c_1680,plain,(
    ! [D_163] : k1_enumset1(D_163,D_163,D_163) = k2_tarski(D_163,D_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_668])).

tff(c_1705,plain,(
    ! [D_167] : k1_enumset1(D_167,D_167,D_167) = k1_tarski(D_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1680])).

tff(c_54,plain,(
    ! [A_40,B_41,C_42,D_43] : k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k1_tarski(D_43)) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1717,plain,(
    ! [D_167,D_43] : k2_xboole_0(k1_tarski(D_167),k1_tarski(D_43)) = k2_enumset1(D_167,D_167,D_167,D_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_54])).

tff(c_1820,plain,(
    ! [D_173,D_174] : k2_enumset1(D_173,D_173,D_173,D_174) = k2_tarski(D_173,D_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1717])).

tff(c_677,plain,(
    ! [A_49,C_114,D_115] : k2_enumset1(A_49,A_49,C_114,D_115) = k1_enumset1(A_49,C_114,D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_671])).

tff(c_1830,plain,(
    ! [D_173,D_174] : k1_enumset1(D_173,D_173,D_174) = k2_tarski(D_173,D_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_677])).

tff(c_60,plain,(
    k1_enumset1('#skF_4','#skF_4','#skF_5') != k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1830,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:14:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.61  
% 3.26/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.61  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.26/1.61  
% 3.26/1.61  %Foreground sorts:
% 3.26/1.61  
% 3.26/1.61  
% 3.26/1.61  %Background operators:
% 3.26/1.61  
% 3.26/1.61  
% 3.26/1.61  %Foreground operators:
% 3.26/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.26/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.26/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.61  
% 3.26/1.63  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.26/1.63  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.63  tff(f_68, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.26/1.63  tff(f_64, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.26/1.63  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.26/1.63  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.63  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.26/1.63  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.26/1.63  tff(f_72, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.26/1.63  tff(f_79, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.63  tff(c_48, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(B_32))=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.63  tff(c_58, plain, (![A_49]: (k2_tarski(A_49, A_49)=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.63  tff(c_50, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(B_34, C_35))=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.63  tff(c_654, plain, (![A_112, B_113, C_114, D_115]: (k2_xboole_0(k2_tarski(A_112, B_113), k2_tarski(C_114, D_115))=k2_enumset1(A_112, B_113, C_114, D_115))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.26/1.63  tff(c_671, plain, (![A_49, C_114, D_115]: (k2_xboole_0(k1_tarski(A_49), k2_tarski(C_114, D_115))=k2_enumset1(A_49, A_49, C_114, D_115))), inference(superposition, [status(thm), theory('equality')], [c_58, c_654])).
% 3.26/1.63  tff(c_1673, plain, (![A_161, C_162, D_163]: (k2_enumset1(A_161, A_161, C_162, D_163)=k1_enumset1(A_161, C_162, D_163))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_671])).
% 3.26/1.63  tff(c_38, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.63  tff(c_194, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.63  tff(c_215, plain, (![A_69]: (k4_xboole_0(A_69, A_69)=k3_xboole_0(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_194])).
% 3.26/1.63  tff(c_44, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.63  tff(c_561, plain, (![A_110]: (k5_xboole_0(A_110, k3_xboole_0(A_110, k1_xboole_0))=k2_xboole_0(A_110, A_110))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 3.26/1.63  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.63  tff(c_582, plain, (![A_110]: (k4_xboole_0(A_110, k1_xboole_0)=k2_xboole_0(A_110, A_110))), inference(superposition, [status(thm), theory('equality')], [c_561, c_34])).
% 3.26/1.63  tff(c_617, plain, (![A_110]: (k2_xboole_0(A_110, A_110)=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_582])).
% 3.26/1.63  tff(c_668, plain, (![A_112, B_113]: (k2_enumset1(A_112, B_113, A_112, B_113)=k2_tarski(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_617, c_654])).
% 3.26/1.63  tff(c_1680, plain, (![D_163]: (k1_enumset1(D_163, D_163, D_163)=k2_tarski(D_163, D_163))), inference(superposition, [status(thm), theory('equality')], [c_1673, c_668])).
% 3.26/1.63  tff(c_1705, plain, (![D_167]: (k1_enumset1(D_167, D_167, D_167)=k1_tarski(D_167))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1680])).
% 3.26/1.63  tff(c_54, plain, (![A_40, B_41, C_42, D_43]: (k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k1_tarski(D_43))=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.63  tff(c_1717, plain, (![D_167, D_43]: (k2_xboole_0(k1_tarski(D_167), k1_tarski(D_43))=k2_enumset1(D_167, D_167, D_167, D_43))), inference(superposition, [status(thm), theory('equality')], [c_1705, c_54])).
% 3.26/1.63  tff(c_1820, plain, (![D_173, D_174]: (k2_enumset1(D_173, D_173, D_173, D_174)=k2_tarski(D_173, D_174))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1717])).
% 3.26/1.63  tff(c_677, plain, (![A_49, C_114, D_115]: (k2_enumset1(A_49, A_49, C_114, D_115)=k1_enumset1(A_49, C_114, D_115))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_671])).
% 3.26/1.63  tff(c_1830, plain, (![D_173, D_174]: (k1_enumset1(D_173, D_173, D_174)=k2_tarski(D_173, D_174))), inference(superposition, [status(thm), theory('equality')], [c_1820, c_677])).
% 3.26/1.63  tff(c_60, plain, (k1_enumset1('#skF_4', '#skF_4', '#skF_5')!=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.63  tff(c_1858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1830, c_60])).
% 3.26/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.63  
% 3.26/1.63  Inference rules
% 3.26/1.63  ----------------------
% 3.26/1.63  #Ref     : 0
% 3.26/1.63  #Sup     : 413
% 3.26/1.63  #Fact    : 0
% 3.26/1.63  #Define  : 0
% 3.26/1.63  #Split   : 0
% 3.26/1.63  #Chain   : 0
% 3.26/1.63  #Close   : 0
% 3.26/1.63  
% 3.26/1.63  Ordering : KBO
% 3.26/1.63  
% 3.26/1.63  Simplification rules
% 3.26/1.63  ----------------------
% 3.26/1.63  #Subsume      : 23
% 3.26/1.63  #Demod        : 280
% 3.26/1.63  #Tautology    : 246
% 3.26/1.63  #SimpNegUnit  : 0
% 3.26/1.63  #BackRed      : 5
% 3.26/1.63  
% 3.26/1.63  #Partial instantiations: 0
% 3.26/1.63  #Strategies tried      : 1
% 3.26/1.63  
% 3.26/1.63  Timing (in seconds)
% 3.26/1.63  ----------------------
% 3.26/1.63  Preprocessing        : 0.34
% 3.26/1.63  Parsing              : 0.18
% 3.26/1.63  CNF conversion       : 0.02
% 3.26/1.63  Main loop            : 0.48
% 3.26/1.63  Inferencing          : 0.17
% 3.26/1.63  Reduction            : 0.17
% 3.26/1.63  Demodulation         : 0.14
% 3.26/1.63  BG Simplification    : 0.03
% 3.26/1.63  Subsumption          : 0.08
% 3.26/1.63  Abstraction          : 0.02
% 3.26/1.63  MUC search           : 0.00
% 3.26/1.63  Cooper               : 0.00
% 3.26/1.63  Total                : 0.85
% 3.26/1.63  Index Insertion      : 0.00
% 3.26/1.63  Index Deletion       : 0.00
% 3.26/1.63  Index Matching       : 0.00
% 3.26/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
