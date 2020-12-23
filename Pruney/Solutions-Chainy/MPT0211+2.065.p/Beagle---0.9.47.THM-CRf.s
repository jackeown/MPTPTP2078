%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:23 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 125 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   39 ( 109 expanded)
%              Number of equality atoms :   38 ( 108 expanded)
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

tff(f_55,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_30,plain,(
    ! [A_59,C_61,B_60] : k1_enumset1(A_59,C_61,B_60) = k1_enumset1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_47,B_48,C_49] : k2_enumset1(A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_50,B_51,C_52,D_53] : k3_enumset1(A_50,A_50,B_51,C_52,D_53) = k2_enumset1(A_50,B_51,C_52,D_53) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_559,plain,(
    ! [B_92,E_91,D_94,C_90,A_93] : k2_xboole_0(k2_enumset1(A_93,B_92,C_90,D_94),k1_tarski(E_91)) = k3_enumset1(A_93,B_92,C_90,D_94,E_91) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_568,plain,(
    ! [A_47,B_48,C_49,E_91] : k3_enumset1(A_47,A_47,B_48,C_49,E_91) = k2_xboole_0(k1_enumset1(A_47,B_48,C_49),k1_tarski(E_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_559])).

tff(c_572,plain,(
    ! [A_95,B_96,C_97,E_98] : k2_xboole_0(k1_enumset1(A_95,B_96,C_97),k1_tarski(E_98)) = k2_enumset1(A_95,B_96,C_97,E_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_568])).

tff(c_611,plain,(
    ! [A_45,B_46,E_98] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(E_98)) = k2_enumset1(A_45,A_45,B_46,E_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_572])).

tff(c_614,plain,(
    ! [A_45,B_46,E_98] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(E_98)) = k1_enumset1(A_45,B_46,E_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_611])).

tff(c_61,plain,(
    ! [B_67,C_68,A_69] : k1_enumset1(B_67,C_68,A_69) = k1_enumset1(A_69,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [B_67,C_68] : k1_enumset1(B_67,C_68,B_67) = k2_tarski(B_67,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_22])).

tff(c_602,plain,(
    ! [B_67,C_68,E_98] : k2_xboole_0(k2_tarski(B_67,C_68),k1_tarski(E_98)) = k2_enumset1(B_67,C_68,B_67,E_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_572])).

tff(c_854,plain,(
    ! [B_67,C_68,E_98] : k2_enumset1(B_67,C_68,B_67,E_98) = k1_enumset1(B_67,C_68,E_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_602])).

tff(c_615,plain,(
    ! [E_99,C_102,B_103,D_100,A_101] : k2_xboole_0(k1_enumset1(A_101,B_103,C_102),k2_tarski(D_100,E_99)) = k3_enumset1(A_101,B_103,C_102,D_100,E_99) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_654,plain,(
    ! [A_45,B_46,D_100,E_99] : k3_enumset1(A_45,A_45,B_46,D_100,E_99) = k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(D_100,E_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_615])).

tff(c_660,plain,(
    ! [A_45,B_46,D_100,E_99] : k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(D_100,E_99)) = k2_enumset1(A_45,B_46,D_100,E_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_654])).

tff(c_81,plain,(
    ! [A_69,C_68] : k1_enumset1(A_69,C_68,C_68) = k2_tarski(C_68,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_22])).

tff(c_571,plain,(
    ! [A_47,B_48,C_49,E_91] : k2_xboole_0(k1_enumset1(A_47,B_48,C_49),k1_tarski(E_91)) = k2_enumset1(A_47,B_48,C_49,E_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_568])).

tff(c_20,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_657,plain,(
    ! [A_101,B_103,C_102,A_44] : k3_enumset1(A_101,B_103,C_102,A_44,A_44) = k2_xboole_0(k1_enumset1(A_101,B_103,C_102),k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_615])).

tff(c_684,plain,(
    ! [A_109,B_110,C_111,A_112] : k3_enumset1(A_109,B_110,C_111,A_112,A_112) = k2_enumset1(A_109,B_110,C_111,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_657])).

tff(c_691,plain,(
    ! [B_110,C_111,A_112] : k2_enumset1(B_110,C_111,A_112,A_112) = k2_enumset1(B_110,B_110,C_111,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_26])).

tff(c_703,plain,(
    ! [B_113,C_114,A_115] : k2_enumset1(B_113,C_114,A_115,A_115) = k1_enumset1(B_113,C_114,A_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_691])).

tff(c_713,plain,(
    ! [C_114,A_115] : k1_enumset1(C_114,C_114,A_115) = k1_enumset1(C_114,A_115,A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_24])).

tff(c_723,plain,(
    ! [C_114,A_115] : k2_tarski(C_114,A_115) = k2_tarski(A_115,C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_22,c_713])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_726,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_723,c_33])).

tff(c_1410,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_726])).

tff(c_1413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_854,c_1410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.21/1.50  
% 3.21/1.50  %Foreground sorts:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Background operators:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Foreground operators:
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.50  
% 3.21/1.51  tff(f_55, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 3.21/1.51  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.21/1.51  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.21/1.51  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.21/1.51  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.21/1.51  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 3.21/1.51  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 3.21/1.51  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.51  tff(f_58, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.21/1.51  tff(c_30, plain, (![A_59, C_61, B_60]: (k1_enumset1(A_59, C_61, B_60)=k1_enumset1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.51  tff(c_24, plain, (![A_47, B_48, C_49]: (k2_enumset1(A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.51  tff(c_22, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.51  tff(c_26, plain, (![A_50, B_51, C_52, D_53]: (k3_enumset1(A_50, A_50, B_51, C_52, D_53)=k2_enumset1(A_50, B_51, C_52, D_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.51  tff(c_559, plain, (![B_92, E_91, D_94, C_90, A_93]: (k2_xboole_0(k2_enumset1(A_93, B_92, C_90, D_94), k1_tarski(E_91))=k3_enumset1(A_93, B_92, C_90, D_94, E_91))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.51  tff(c_568, plain, (![A_47, B_48, C_49, E_91]: (k3_enumset1(A_47, A_47, B_48, C_49, E_91)=k2_xboole_0(k1_enumset1(A_47, B_48, C_49), k1_tarski(E_91)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_559])).
% 3.21/1.51  tff(c_572, plain, (![A_95, B_96, C_97, E_98]: (k2_xboole_0(k1_enumset1(A_95, B_96, C_97), k1_tarski(E_98))=k2_enumset1(A_95, B_96, C_97, E_98))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_568])).
% 3.21/1.51  tff(c_611, plain, (![A_45, B_46, E_98]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(E_98))=k2_enumset1(A_45, A_45, B_46, E_98))), inference(superposition, [status(thm), theory('equality')], [c_22, c_572])).
% 3.21/1.51  tff(c_614, plain, (![A_45, B_46, E_98]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(E_98))=k1_enumset1(A_45, B_46, E_98))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_611])).
% 3.21/1.51  tff(c_61, plain, (![B_67, C_68, A_69]: (k1_enumset1(B_67, C_68, A_69)=k1_enumset1(A_69, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.51  tff(c_77, plain, (![B_67, C_68]: (k1_enumset1(B_67, C_68, B_67)=k2_tarski(B_67, C_68))), inference(superposition, [status(thm), theory('equality')], [c_61, c_22])).
% 3.21/1.51  tff(c_602, plain, (![B_67, C_68, E_98]: (k2_xboole_0(k2_tarski(B_67, C_68), k1_tarski(E_98))=k2_enumset1(B_67, C_68, B_67, E_98))), inference(superposition, [status(thm), theory('equality')], [c_77, c_572])).
% 3.21/1.51  tff(c_854, plain, (![B_67, C_68, E_98]: (k2_enumset1(B_67, C_68, B_67, E_98)=k1_enumset1(B_67, C_68, E_98))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_602])).
% 3.21/1.51  tff(c_615, plain, (![E_99, C_102, B_103, D_100, A_101]: (k2_xboole_0(k1_enumset1(A_101, B_103, C_102), k2_tarski(D_100, E_99))=k3_enumset1(A_101, B_103, C_102, D_100, E_99))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.51  tff(c_654, plain, (![A_45, B_46, D_100, E_99]: (k3_enumset1(A_45, A_45, B_46, D_100, E_99)=k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(D_100, E_99)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_615])).
% 3.21/1.51  tff(c_660, plain, (![A_45, B_46, D_100, E_99]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(D_100, E_99))=k2_enumset1(A_45, B_46, D_100, E_99))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_654])).
% 3.21/1.51  tff(c_81, plain, (![A_69, C_68]: (k1_enumset1(A_69, C_68, C_68)=k2_tarski(C_68, A_69))), inference(superposition, [status(thm), theory('equality')], [c_61, c_22])).
% 3.21/1.51  tff(c_571, plain, (![A_47, B_48, C_49, E_91]: (k2_xboole_0(k1_enumset1(A_47, B_48, C_49), k1_tarski(E_91))=k2_enumset1(A_47, B_48, C_49, E_91))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_568])).
% 3.21/1.51  tff(c_20, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.51  tff(c_657, plain, (![A_101, B_103, C_102, A_44]: (k3_enumset1(A_101, B_103, C_102, A_44, A_44)=k2_xboole_0(k1_enumset1(A_101, B_103, C_102), k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_615])).
% 3.21/1.51  tff(c_684, plain, (![A_109, B_110, C_111, A_112]: (k3_enumset1(A_109, B_110, C_111, A_112, A_112)=k2_enumset1(A_109, B_110, C_111, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_657])).
% 3.21/1.51  tff(c_691, plain, (![B_110, C_111, A_112]: (k2_enumset1(B_110, C_111, A_112, A_112)=k2_enumset1(B_110, B_110, C_111, A_112))), inference(superposition, [status(thm), theory('equality')], [c_684, c_26])).
% 3.21/1.51  tff(c_703, plain, (![B_113, C_114, A_115]: (k2_enumset1(B_113, C_114, A_115, A_115)=k1_enumset1(B_113, C_114, A_115))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_691])).
% 3.21/1.51  tff(c_713, plain, (![C_114, A_115]: (k1_enumset1(C_114, C_114, A_115)=k1_enumset1(C_114, A_115, A_115))), inference(superposition, [status(thm), theory('equality')], [c_703, c_24])).
% 3.21/1.51  tff(c_723, plain, (![C_114, A_115]: (k2_tarski(C_114, A_115)=k2_tarski(A_115, C_114))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_22, c_713])).
% 3.21/1.51  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.51  tff(c_33, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.21/1.51  tff(c_726, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_723, c_33])).
% 3.21/1.51  tff(c_1410, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_660, c_726])).
% 3.21/1.51  tff(c_1413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_854, c_1410])).
% 3.21/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  Inference rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Ref     : 0
% 3.21/1.51  #Sup     : 345
% 3.21/1.51  #Fact    : 0
% 3.21/1.51  #Define  : 0
% 3.21/1.51  #Split   : 0
% 3.21/1.51  #Chain   : 0
% 3.21/1.51  #Close   : 0
% 3.21/1.51  
% 3.21/1.51  Ordering : KBO
% 3.21/1.51  
% 3.21/1.51  Simplification rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Subsume      : 76
% 3.21/1.51  #Demod        : 197
% 3.21/1.51  #Tautology    : 189
% 3.21/1.51  #SimpNegUnit  : 0
% 3.21/1.51  #BackRed      : 2
% 3.21/1.51  
% 3.21/1.51  #Partial instantiations: 0
% 3.21/1.51  #Strategies tried      : 1
% 3.21/1.51  
% 3.21/1.51  Timing (in seconds)
% 3.21/1.51  ----------------------
% 3.21/1.51  Preprocessing        : 0.32
% 3.21/1.51  Parsing              : 0.18
% 3.21/1.51  CNF conversion       : 0.02
% 3.21/1.51  Main loop            : 0.42
% 3.21/1.51  Inferencing          : 0.15
% 3.21/1.51  Reduction            : 0.18
% 3.21/1.51  Demodulation         : 0.15
% 3.21/1.51  BG Simplification    : 0.02
% 3.21/1.51  Subsumption          : 0.05
% 3.21/1.51  Abstraction          : 0.03
% 3.21/1.51  MUC search           : 0.00
% 3.21/1.51  Cooper               : 0.00
% 3.21/1.51  Total                : 0.77
% 3.21/1.52  Index Insertion      : 0.00
% 3.21/1.52  Index Deletion       : 0.00
% 3.21/1.52  Index Matching       : 0.00
% 3.21/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
