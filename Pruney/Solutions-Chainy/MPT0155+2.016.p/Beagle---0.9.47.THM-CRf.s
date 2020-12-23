%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:10 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 174 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :   41 ( 158 expanded)
%              Number of equality atoms :   40 ( 157 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_10,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(C_18)) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_331,plain,(
    ! [E_83,C_85,D_87,A_84,B_86] : k2_xboole_0(k2_tarski(A_84,B_86),k1_enumset1(C_85,D_87,E_83)) = k3_enumset1(A_84,B_86,C_85,D_87,E_83) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k2_tarski(A_51,B_52),k1_tarski(C_53)) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k2_tarski(A_51,B_52),k1_enumset1(A_51,B_52,C_53)) = k2_xboole_0(k2_tarski(A_51,B_52),k1_tarski(C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2])).

tff(c_83,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k2_tarski(A_51,B_52),k1_enumset1(A_51,B_52,C_53)) = k1_enumset1(A_51,B_52,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_386,plain,(
    ! [C_90,D_91,E_92] : k3_enumset1(C_90,D_91,C_90,D_91,E_92) = k1_enumset1(C_90,D_91,E_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_83])).

tff(c_22,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [A_41,C_53] : k2_xboole_0(k1_tarski(A_41),k1_tarski(C_53)) = k1_enumset1(A_41,A_41,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_69])).

tff(c_85,plain,(
    ! [A_41,C_53] : k2_xboole_0(k1_tarski(A_41),k1_tarski(C_53)) = k2_tarski(A_41,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_81])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61,D_62] : k2_xboole_0(k1_tarski(A_59),k1_enumset1(B_60,C_61,D_62)) = k2_enumset1(A_59,B_60,C_61,D_62) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [A_63,A_64,B_65] : k2_xboole_0(k1_tarski(A_63),k2_tarski(A_64,B_65)) = k2_enumset1(A_63,A_64,A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_179,plain,(
    ! [A_63,A_41] : k2_xboole_0(k1_tarski(A_63),k1_tarski(A_41)) = k2_enumset1(A_63,A_41,A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_154])).

tff(c_184,plain,(
    ! [A_63,A_41] : k2_enumset1(A_63,A_41,A_41,A_41) = k2_tarski(A_63,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_179])).

tff(c_253,plain,(
    ! [B_75,A_77,C_73,E_74,D_76] : k2_xboole_0(k1_tarski(A_77),k2_enumset1(B_75,C_73,D_76,E_74)) = k3_enumset1(A_77,B_75,C_73,D_76,E_74) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_275,plain,(
    ! [A_78,A_79,A_80] : k3_enumset1(A_78,A_79,A_80,A_80,A_80) = k2_xboole_0(k1_tarski(A_78),k2_tarski(A_79,A_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_253])).

tff(c_306,plain,(
    ! [A_78,A_41] : k3_enumset1(A_78,A_41,A_41,A_41,A_41) = k2_xboole_0(k1_tarski(A_78),k1_tarski(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_275])).

tff(c_311,plain,(
    ! [A_78,A_41] : k3_enumset1(A_78,A_41,A_41,A_41,A_41) = k2_tarski(A_78,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_306])).

tff(c_393,plain,(
    ! [E_92] : k1_enumset1(E_92,E_92,E_92) = k2_tarski(E_92,E_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_311])).

tff(c_425,plain,(
    ! [E_93] : k1_enumset1(E_93,E_93,E_93) = k1_tarski(E_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_393])).

tff(c_16,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k2_xboole_0(k2_tarski(A_28,B_29),k1_enumset1(C_30,D_31,E_32)) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_431,plain,(
    ! [A_28,B_29,E_93] : k3_enumset1(A_28,B_29,E_93,E_93,E_93) = k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(E_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_16])).

tff(c_449,plain,(
    ! [A_28,B_29,E_93] : k3_enumset1(A_28,B_29,E_93,E_93,E_93) = k1_enumset1(A_28,B_29,E_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_431])).

tff(c_268,plain,(
    ! [A_77,A_63,A_41] : k3_enumset1(A_77,A_63,A_41,A_41,A_41) = k2_xboole_0(k1_tarski(A_77),k2_tarski(A_63,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_253])).

tff(c_481,plain,(
    ! [A_77,A_63,A_41] : k2_xboole_0(k1_tarski(A_77),k2_tarski(A_63,A_41)) = k1_enumset1(A_77,A_63,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_268])).

tff(c_596,plain,(
    ! [A_110,A_111,A_112] : k2_xboole_0(k1_tarski(A_110),k2_tarski(A_111,A_112)) = k1_enumset1(A_110,A_111,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_268])).

tff(c_606,plain,(
    ! [A_110,A_111,A_112] : k2_xboole_0(k1_tarski(A_110),k1_enumset1(A_110,A_111,A_112)) = k2_xboole_0(k1_tarski(A_110),k2_tarski(A_111,A_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_2])).

tff(c_833,plain,(
    ! [A_134,A_135,A_136] : k2_xboole_0(k1_tarski(A_134),k1_enumset1(A_134,A_135,A_136)) = k1_enumset1(A_134,A_135,A_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_606])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_tarski(A_19),k1_enumset1(B_20,C_21,D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_839,plain,(
    ! [A_134,A_135,A_136] : k2_enumset1(A_134,A_134,A_135,A_136) = k1_enumset1(A_134,A_135,A_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_12])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.30  
% 2.51/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.30  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.51/1.30  
% 2.51/1.30  %Foreground sorts:
% 2.51/1.30  
% 2.51/1.30  
% 2.51/1.30  %Background operators:
% 2.51/1.30  
% 2.51/1.30  
% 2.51/1.30  %Foreground operators:
% 2.51/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.30  
% 2.51/1.32  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.51/1.32  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.51/1.32  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.51/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 2.51/1.32  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.51/1.32  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.51/1.32  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.51/1.32  tff(f_50, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.51/1.32  tff(c_10, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(C_18))=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.32  tff(c_20, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.32  tff(c_331, plain, (![E_83, C_85, D_87, A_84, B_86]: (k2_xboole_0(k2_tarski(A_84, B_86), k1_enumset1(C_85, D_87, E_83))=k3_enumset1(A_84, B_86, C_85, D_87, E_83))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.32  tff(c_69, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k2_tarski(A_51, B_52), k1_tarski(C_53))=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.32  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.32  tff(c_75, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k2_tarski(A_51, B_52), k1_enumset1(A_51, B_52, C_53))=k2_xboole_0(k2_tarski(A_51, B_52), k1_tarski(C_53)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_2])).
% 2.51/1.32  tff(c_83, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k2_tarski(A_51, B_52), k1_enumset1(A_51, B_52, C_53))=k1_enumset1(A_51, B_52, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_75])).
% 2.51/1.32  tff(c_386, plain, (![C_90, D_91, E_92]: (k3_enumset1(C_90, D_91, C_90, D_91, E_92)=k1_enumset1(C_90, D_91, E_92))), inference(superposition, [status(thm), theory('equality')], [c_331, c_83])).
% 2.51/1.32  tff(c_22, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.32  tff(c_81, plain, (![A_41, C_53]: (k2_xboole_0(k1_tarski(A_41), k1_tarski(C_53))=k1_enumset1(A_41, A_41, C_53))), inference(superposition, [status(thm), theory('equality')], [c_20, c_69])).
% 2.51/1.32  tff(c_85, plain, (![A_41, C_53]: (k2_xboole_0(k1_tarski(A_41), k1_tarski(C_53))=k2_tarski(A_41, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_81])).
% 2.51/1.32  tff(c_138, plain, (![A_59, B_60, C_61, D_62]: (k2_xboole_0(k1_tarski(A_59), k1_enumset1(B_60, C_61, D_62))=k2_enumset1(A_59, B_60, C_61, D_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.32  tff(c_154, plain, (![A_63, A_64, B_65]: (k2_xboole_0(k1_tarski(A_63), k2_tarski(A_64, B_65))=k2_enumset1(A_63, A_64, A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_22, c_138])).
% 2.51/1.32  tff(c_179, plain, (![A_63, A_41]: (k2_xboole_0(k1_tarski(A_63), k1_tarski(A_41))=k2_enumset1(A_63, A_41, A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_20, c_154])).
% 2.51/1.32  tff(c_184, plain, (![A_63, A_41]: (k2_enumset1(A_63, A_41, A_41, A_41)=k2_tarski(A_63, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_179])).
% 2.51/1.32  tff(c_253, plain, (![B_75, A_77, C_73, E_74, D_76]: (k2_xboole_0(k1_tarski(A_77), k2_enumset1(B_75, C_73, D_76, E_74))=k3_enumset1(A_77, B_75, C_73, D_76, E_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.32  tff(c_275, plain, (![A_78, A_79, A_80]: (k3_enumset1(A_78, A_79, A_80, A_80, A_80)=k2_xboole_0(k1_tarski(A_78), k2_tarski(A_79, A_80)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_253])).
% 2.51/1.32  tff(c_306, plain, (![A_78, A_41]: (k3_enumset1(A_78, A_41, A_41, A_41, A_41)=k2_xboole_0(k1_tarski(A_78), k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_275])).
% 2.51/1.32  tff(c_311, plain, (![A_78, A_41]: (k3_enumset1(A_78, A_41, A_41, A_41, A_41)=k2_tarski(A_78, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_306])).
% 2.51/1.32  tff(c_393, plain, (![E_92]: (k1_enumset1(E_92, E_92, E_92)=k2_tarski(E_92, E_92))), inference(superposition, [status(thm), theory('equality')], [c_386, c_311])).
% 2.51/1.32  tff(c_425, plain, (![E_93]: (k1_enumset1(E_93, E_93, E_93)=k1_tarski(E_93))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_393])).
% 2.51/1.32  tff(c_16, plain, (![C_30, E_32, D_31, B_29, A_28]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_enumset1(C_30, D_31, E_32))=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.32  tff(c_431, plain, (![A_28, B_29, E_93]: (k3_enumset1(A_28, B_29, E_93, E_93, E_93)=k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(E_93)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_16])).
% 2.51/1.32  tff(c_449, plain, (![A_28, B_29, E_93]: (k3_enumset1(A_28, B_29, E_93, E_93, E_93)=k1_enumset1(A_28, B_29, E_93))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_431])).
% 2.51/1.32  tff(c_268, plain, (![A_77, A_63, A_41]: (k3_enumset1(A_77, A_63, A_41, A_41, A_41)=k2_xboole_0(k1_tarski(A_77), k2_tarski(A_63, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_253])).
% 2.51/1.32  tff(c_481, plain, (![A_77, A_63, A_41]: (k2_xboole_0(k1_tarski(A_77), k2_tarski(A_63, A_41))=k1_enumset1(A_77, A_63, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_268])).
% 2.51/1.32  tff(c_596, plain, (![A_110, A_111, A_112]: (k2_xboole_0(k1_tarski(A_110), k2_tarski(A_111, A_112))=k1_enumset1(A_110, A_111, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_268])).
% 2.51/1.32  tff(c_606, plain, (![A_110, A_111, A_112]: (k2_xboole_0(k1_tarski(A_110), k1_enumset1(A_110, A_111, A_112))=k2_xboole_0(k1_tarski(A_110), k2_tarski(A_111, A_112)))), inference(superposition, [status(thm), theory('equality')], [c_596, c_2])).
% 2.51/1.32  tff(c_833, plain, (![A_134, A_135, A_136]: (k2_xboole_0(k1_tarski(A_134), k1_enumset1(A_134, A_135, A_136))=k1_enumset1(A_134, A_135, A_136))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_606])).
% 2.51/1.32  tff(c_12, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_tarski(A_19), k1_enumset1(B_20, C_21, D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.32  tff(c_839, plain, (![A_134, A_135, A_136]: (k2_enumset1(A_134, A_134, A_135, A_136)=k1_enumset1(A_134, A_135, A_136))), inference(superposition, [status(thm), theory('equality')], [c_833, c_12])).
% 2.51/1.32  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.32  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_839, c_24])).
% 2.51/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.32  
% 2.51/1.32  Inference rules
% 2.51/1.32  ----------------------
% 2.51/1.32  #Ref     : 0
% 2.51/1.32  #Sup     : 194
% 2.51/1.32  #Fact    : 0
% 2.51/1.32  #Define  : 0
% 2.51/1.32  #Split   : 0
% 2.51/1.32  #Chain   : 0
% 2.51/1.32  #Close   : 0
% 2.51/1.32  
% 2.51/1.32  Ordering : KBO
% 2.51/1.32  
% 2.51/1.32  Simplification rules
% 2.51/1.32  ----------------------
% 2.51/1.32  #Subsume      : 0
% 2.51/1.32  #Demod        : 178
% 2.51/1.32  #Tautology    : 148
% 2.51/1.32  #SimpNegUnit  : 0
% 2.51/1.32  #BackRed      : 3
% 2.51/1.32  
% 2.51/1.32  #Partial instantiations: 0
% 2.51/1.32  #Strategies tried      : 1
% 2.51/1.32  
% 2.51/1.32  Timing (in seconds)
% 2.51/1.32  ----------------------
% 2.51/1.32  Preprocessing        : 0.30
% 2.51/1.32  Parsing              : 0.17
% 2.51/1.32  CNF conversion       : 0.02
% 2.51/1.32  Main loop            : 0.30
% 2.51/1.32  Inferencing          : 0.13
% 2.51/1.32  Reduction            : 0.11
% 2.51/1.32  Demodulation         : 0.09
% 2.51/1.32  BG Simplification    : 0.02
% 2.51/1.32  Subsumption          : 0.03
% 2.51/1.32  Abstraction          : 0.02
% 2.51/1.32  MUC search           : 0.00
% 2.51/1.32  Cooper               : 0.00
% 2.51/1.32  Total                : 0.63
% 2.51/1.32  Index Insertion      : 0.00
% 2.51/1.32  Index Deletion       : 0.00
% 2.51/1.32  Index Matching       : 0.00
% 2.51/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
