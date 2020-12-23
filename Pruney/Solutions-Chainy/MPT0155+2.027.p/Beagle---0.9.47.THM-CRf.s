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
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :   29 (  59 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_8,B_9),k1_tarski(C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_160,plain,(
    ! [B_70,C_68,A_72,E_71,D_69] : k2_xboole_0(k2_tarski(A_72,B_70),k1_enumset1(C_68,D_69,E_71)) = k3_enumset1(A_72,B_70,C_68,D_69,E_71) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_188,plain,(
    ! [A_77,B_78,A_79,B_80] : k3_enumset1(A_77,B_78,A_79,A_79,B_80) = k2_xboole_0(k2_tarski(A_77,B_78),k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_160])).

tff(c_214,plain,(
    ! [A_77,B_78,A_38] : k3_enumset1(A_77,B_78,A_38,A_38,A_38) = k2_xboole_0(k2_tarski(A_77,B_78),k1_tarski(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_265,plain,(
    ! [A_89,B_90,A_91] : k3_enumset1(A_89,B_90,A_91,A_91,A_91) = k1_enumset1(A_89,B_90,A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_214])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_38,C_68,D_69,E_71] : k3_enumset1(A_38,A_38,C_68,D_69,E_71) = k2_xboole_0(k1_tarski(A_38),k1_enumset1(C_68,D_69,E_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_160])).

tff(c_178,plain,(
    ! [A_38,C_68,D_69,E_71] : k3_enumset1(A_38,A_38,C_68,D_69,E_71) = k2_enumset1(A_38,C_68,D_69,E_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_175])).

tff(c_279,plain,(
    ! [B_90,A_91] : k2_enumset1(B_90,A_91,A_91,A_91) = k1_enumset1(B_90,B_90,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_178])).

tff(c_303,plain,(
    ! [B_92,A_93] : k2_enumset1(B_92,A_93,A_93,A_93) = k2_tarski(B_92,A_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_279])).

tff(c_14,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] : k2_xboole_0(k2_enumset1(A_20,B_21,C_22,D_23),k1_tarski(E_24)) = k3_enumset1(A_20,B_21,C_22,D_23,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_309,plain,(
    ! [B_92,A_93,E_24] : k3_enumset1(B_92,A_93,A_93,A_93,E_24) = k2_xboole_0(k2_tarski(B_92,A_93),k1_tarski(E_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_14])).

tff(c_357,plain,(
    ! [B_100,A_101,E_102] : k3_enumset1(B_100,A_101,A_101,A_101,E_102) = k1_enumset1(B_100,A_101,E_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_309])).

tff(c_378,plain,(
    ! [A_101,E_102] : k2_enumset1(A_101,A_101,A_101,E_102) = k1_enumset1(A_101,A_101,E_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_178])).

tff(c_406,plain,(
    ! [A_103,E_104] : k2_enumset1(A_103,A_103,A_103,E_104) = k2_tarski(A_103,E_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_378])).

tff(c_416,plain,(
    ! [A_103,E_104,E_24] : k3_enumset1(A_103,A_103,A_103,E_104,E_24) = k2_xboole_0(k2_tarski(A_103,E_104),k1_tarski(E_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_14])).

tff(c_494,plain,(
    ! [A_113,E_114,E_115] : k3_enumset1(A_113,A_113,A_113,E_114,E_115) = k1_enumset1(A_113,E_114,E_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_416])).

tff(c_519,plain,(
    ! [A_113,E_114,E_115] : k2_enumset1(A_113,A_113,E_114,E_115) = k1_enumset1(A_113,E_114,E_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_178])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.29  
% 2.22/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.29  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.22/1.29  
% 2.22/1.29  %Foreground sorts:
% 2.22/1.29  
% 2.22/1.29  
% 2.22/1.29  %Background operators:
% 2.22/1.29  
% 2.22/1.29  
% 2.22/1.29  %Foreground operators:
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.29  
% 2.22/1.30  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.22/1.30  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.22/1.30  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.30  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.22/1.30  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.22/1.30  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.22/1.30  tff(f_50, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.22/1.30  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_tarski(C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.30  tff(c_22, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.30  tff(c_20, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.30  tff(c_160, plain, (![B_70, C_68, A_72, E_71, D_69]: (k2_xboole_0(k2_tarski(A_72, B_70), k1_enumset1(C_68, D_69, E_71))=k3_enumset1(A_72, B_70, C_68, D_69, E_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.30  tff(c_188, plain, (![A_77, B_78, A_79, B_80]: (k3_enumset1(A_77, B_78, A_79, A_79, B_80)=k2_xboole_0(k2_tarski(A_77, B_78), k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_160])).
% 2.22/1.30  tff(c_214, plain, (![A_77, B_78, A_38]: (k3_enumset1(A_77, B_78, A_38, A_38, A_38)=k2_xboole_0(k2_tarski(A_77, B_78), k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 2.22/1.30  tff(c_265, plain, (![A_89, B_90, A_91]: (k3_enumset1(A_89, B_90, A_91, A_91, A_91)=k1_enumset1(A_89, B_90, A_91))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_214])).
% 2.22/1.30  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.30  tff(c_175, plain, (![A_38, C_68, D_69, E_71]: (k3_enumset1(A_38, A_38, C_68, D_69, E_71)=k2_xboole_0(k1_tarski(A_38), k1_enumset1(C_68, D_69, E_71)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_160])).
% 2.22/1.30  tff(c_178, plain, (![A_38, C_68, D_69, E_71]: (k3_enumset1(A_38, A_38, C_68, D_69, E_71)=k2_enumset1(A_38, C_68, D_69, E_71))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_175])).
% 2.22/1.30  tff(c_279, plain, (![B_90, A_91]: (k2_enumset1(B_90, A_91, A_91, A_91)=k1_enumset1(B_90, B_90, A_91))), inference(superposition, [status(thm), theory('equality')], [c_265, c_178])).
% 2.22/1.30  tff(c_303, plain, (![B_92, A_93]: (k2_enumset1(B_92, A_93, A_93, A_93)=k2_tarski(B_92, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_279])).
% 2.22/1.30  tff(c_14, plain, (![C_22, D_23, A_20, B_21, E_24]: (k2_xboole_0(k2_enumset1(A_20, B_21, C_22, D_23), k1_tarski(E_24))=k3_enumset1(A_20, B_21, C_22, D_23, E_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.30  tff(c_309, plain, (![B_92, A_93, E_24]: (k3_enumset1(B_92, A_93, A_93, A_93, E_24)=k2_xboole_0(k2_tarski(B_92, A_93), k1_tarski(E_24)))), inference(superposition, [status(thm), theory('equality')], [c_303, c_14])).
% 2.22/1.30  tff(c_357, plain, (![B_100, A_101, E_102]: (k3_enumset1(B_100, A_101, A_101, A_101, E_102)=k1_enumset1(B_100, A_101, E_102))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_309])).
% 2.22/1.30  tff(c_378, plain, (![A_101, E_102]: (k2_enumset1(A_101, A_101, A_101, E_102)=k1_enumset1(A_101, A_101, E_102))), inference(superposition, [status(thm), theory('equality')], [c_357, c_178])).
% 2.22/1.30  tff(c_406, plain, (![A_103, E_104]: (k2_enumset1(A_103, A_103, A_103, E_104)=k2_tarski(A_103, E_104))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_378])).
% 2.22/1.30  tff(c_416, plain, (![A_103, E_104, E_24]: (k3_enumset1(A_103, A_103, A_103, E_104, E_24)=k2_xboole_0(k2_tarski(A_103, E_104), k1_tarski(E_24)))), inference(superposition, [status(thm), theory('equality')], [c_406, c_14])).
% 2.22/1.30  tff(c_494, plain, (![A_113, E_114, E_115]: (k3_enumset1(A_113, A_113, A_113, E_114, E_115)=k1_enumset1(A_113, E_114, E_115))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_416])).
% 2.22/1.30  tff(c_519, plain, (![A_113, E_114, E_115]: (k2_enumset1(A_113, A_113, E_114, E_115)=k1_enumset1(A_113, E_114, E_115))), inference(superposition, [status(thm), theory('equality')], [c_494, c_178])).
% 2.22/1.30  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.30  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_519, c_24])).
% 2.22/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.30  
% 2.22/1.30  Inference rules
% 2.22/1.30  ----------------------
% 2.22/1.30  #Ref     : 0
% 2.22/1.30  #Sup     : 119
% 2.22/1.30  #Fact    : 0
% 2.22/1.30  #Define  : 0
% 2.22/1.30  #Split   : 0
% 2.22/1.30  #Chain   : 0
% 2.22/1.30  #Close   : 0
% 2.22/1.30  
% 2.22/1.30  Ordering : KBO
% 2.22/1.30  
% 2.22/1.30  Simplification rules
% 2.22/1.30  ----------------------
% 2.22/1.30  #Subsume      : 0
% 2.22/1.30  #Demod        : 98
% 2.22/1.30  #Tautology    : 93
% 2.22/1.30  #SimpNegUnit  : 0
% 2.22/1.30  #BackRed      : 1
% 2.22/1.30  
% 2.22/1.30  #Partial instantiations: 0
% 2.22/1.30  #Strategies tried      : 1
% 2.22/1.30  
% 2.22/1.30  Timing (in seconds)
% 2.22/1.30  ----------------------
% 2.22/1.31  Preprocessing        : 0.30
% 2.22/1.31  Parsing              : 0.16
% 2.22/1.31  CNF conversion       : 0.02
% 2.22/1.31  Main loop            : 0.25
% 2.22/1.31  Inferencing          : 0.11
% 2.22/1.31  Reduction            : 0.09
% 2.22/1.31  Demodulation         : 0.07
% 2.22/1.31  BG Simplification    : 0.02
% 2.22/1.31  Subsumption          : 0.02
% 2.22/1.31  Abstraction          : 0.02
% 2.22/1.31  MUC search           : 0.00
% 2.22/1.31  Cooper               : 0.00
% 2.22/1.31  Total                : 0.58
% 2.22/1.31  Index Insertion      : 0.00
% 2.22/1.31  Index Deletion       : 0.00
% 2.22/1.31  Index Matching       : 0.00
% 2.22/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
