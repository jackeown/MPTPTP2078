%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   52 (  89 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   44 (  87 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_308,plain,(
    ! [A_69,B_70,C_71,D_72] : k2_xboole_0(k2_tarski(A_69,B_70),k2_tarski(C_71,D_72)) = k2_enumset1(A_69,B_70,C_71,D_72) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_339,plain,(
    ! [A_22,C_71,D_72] : k2_xboole_0(k1_tarski(A_22),k2_tarski(C_71,D_72)) = k2_enumset1(A_22,A_22,C_71,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_308])).

tff(c_355,plain,(
    ! [A_22,C_71,D_72] : k2_xboole_0(k1_tarski(A_22),k2_tarski(C_71,D_72)) = k1_enumset1(A_22,C_71,D_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_339])).

tff(c_82,plain,(
    ! [B_43,C_44,A_45] : k1_enumset1(B_43,C_44,A_45) = k1_enumset1(A_45,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [B_24,A_23] : k1_enumset1(B_24,A_23,A_23) = k2_tarski(A_23,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_493,plain,(
    ! [A_82,C_83,D_84] : k2_xboole_0(k1_tarski(A_82),k2_tarski(C_83,D_84)) = k1_enumset1(A_82,C_83,D_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_339])).

tff(c_520,plain,(
    ! [A_82,A_22] : k2_xboole_0(k1_tarski(A_82),k1_tarski(A_22)) = k1_enumset1(A_82,A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_493])).

tff(c_528,plain,(
    ! [A_85,A_86] : k2_xboole_0(k1_tarski(A_85),k1_tarski(A_86)) = k2_tarski(A_86,A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_520])).

tff(c_66,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_41,B_42] : r1_tarski(k4_xboole_0(A_41,B_42),k2_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8])).

tff(c_239,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k2_xboole_0(B_58,C_59))
      | ~ r1_tarski(k4_xboole_0(A_57,B_58),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,k2_xboole_0(A_41,B_42))) ),
    inference(resolution,[status(thm)],[c_72,c_239])).

tff(c_537,plain,(
    ! [A_85,A_86] : r1_tarski(k1_tarski(A_85),k2_xboole_0(k1_tarski(A_86),k2_tarski(A_86,A_85))) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_253])).

tff(c_566,plain,(
    ! [A_87,A_88] : r1_tarski(k1_tarski(A_87),k2_tarski(A_88,A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_355,c_537])).

tff(c_572,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_566])).

tff(c_24,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | ~ r1_tarski(k1_tarski(A_28),k1_tarski(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_577,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_572,c_24])).

tff(c_584,plain,(
    k2_tarski('#skF_2','#skF_1') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_28])).

tff(c_255,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(B_9,A_8)) ),
    inference(resolution,[status(thm)],[c_8,c_239])).

tff(c_609,plain,(
    ! [A_89,A_90] : r1_tarski(k1_tarski(A_89),k2_tarski(A_89,A_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_255])).

tff(c_612,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_609])).

tff(c_619,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_612,c_24])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n011.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 11:05:26 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.26  
% 2.35/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.26  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.35/1.26  
% 2.35/1.26  %Foreground sorts:
% 2.35/1.26  
% 2.35/1.26  
% 2.35/1.26  %Background operators:
% 2.35/1.26  
% 2.35/1.26  
% 2.35/1.26  %Foreground operators:
% 2.35/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.26  
% 2.35/1.27  tff(f_62, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.35/1.27  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.35/1.27  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.35/1.27  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.35/1.27  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.35/1.27  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 2.35/1.27  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.35/1.27  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.35/1.27  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.35/1.27  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.35/1.27  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.27  tff(c_28, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.27  tff(c_20, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.35/1.27  tff(c_22, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.27  tff(c_18, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.27  tff(c_308, plain, (![A_69, B_70, C_71, D_72]: (k2_xboole_0(k2_tarski(A_69, B_70), k2_tarski(C_71, D_72))=k2_enumset1(A_69, B_70, C_71, D_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.27  tff(c_339, plain, (![A_22, C_71, D_72]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(C_71, D_72))=k2_enumset1(A_22, A_22, C_71, D_72))), inference(superposition, [status(thm), theory('equality')], [c_18, c_308])).
% 2.35/1.27  tff(c_355, plain, (![A_22, C_71, D_72]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(C_71, D_72))=k1_enumset1(A_22, C_71, D_72))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_339])).
% 2.35/1.27  tff(c_82, plain, (![B_43, C_44, A_45]: (k1_enumset1(B_43, C_44, A_45)=k1_enumset1(A_45, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.27  tff(c_117, plain, (![B_24, A_23]: (k1_enumset1(B_24, A_23, A_23)=k2_tarski(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_20, c_82])).
% 2.35/1.27  tff(c_493, plain, (![A_82, C_83, D_84]: (k2_xboole_0(k1_tarski(A_82), k2_tarski(C_83, D_84))=k1_enumset1(A_82, C_83, D_84))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_339])).
% 2.35/1.27  tff(c_520, plain, (![A_82, A_22]: (k2_xboole_0(k1_tarski(A_82), k1_tarski(A_22))=k1_enumset1(A_82, A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_18, c_493])).
% 2.35/1.27  tff(c_528, plain, (![A_85, A_86]: (k2_xboole_0(k1_tarski(A_85), k1_tarski(A_86))=k2_tarski(A_86, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_520])).
% 2.35/1.27  tff(c_66, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.27  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.27  tff(c_72, plain, (![A_41, B_42]: (r1_tarski(k4_xboole_0(A_41, B_42), k2_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_8])).
% 2.35/1.27  tff(c_239, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k2_xboole_0(B_58, C_59)) | ~r1_tarski(k4_xboole_0(A_57, B_58), C_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.27  tff(c_253, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, k2_xboole_0(A_41, B_42))))), inference(resolution, [status(thm)], [c_72, c_239])).
% 2.35/1.27  tff(c_537, plain, (![A_85, A_86]: (r1_tarski(k1_tarski(A_85), k2_xboole_0(k1_tarski(A_86), k2_tarski(A_86, A_85))))), inference(superposition, [status(thm), theory('equality')], [c_528, c_253])).
% 2.35/1.27  tff(c_566, plain, (![A_87, A_88]: (r1_tarski(k1_tarski(A_87), k2_tarski(A_88, A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_355, c_537])).
% 2.35/1.27  tff(c_572, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_566])).
% 2.35/1.27  tff(c_24, plain, (![B_29, A_28]: (B_29=A_28 | ~r1_tarski(k1_tarski(A_28), k1_tarski(B_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.27  tff(c_577, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_572, c_24])).
% 2.35/1.27  tff(c_584, plain, (k2_tarski('#skF_2', '#skF_1')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_28])).
% 2.35/1.27  tff(c_255, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(B_9, A_8)))), inference(resolution, [status(thm)], [c_8, c_239])).
% 2.35/1.27  tff(c_609, plain, (![A_89, A_90]: (r1_tarski(k1_tarski(A_89), k2_tarski(A_89, A_90)))), inference(superposition, [status(thm), theory('equality')], [c_528, c_255])).
% 2.35/1.27  tff(c_612, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_584, c_609])).
% 2.35/1.27  tff(c_619, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_612, c_24])).
% 2.35/1.27  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_619])).
% 2.35/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.27  
% 2.35/1.27  Inference rules
% 2.35/1.27  ----------------------
% 2.35/1.27  #Ref     : 1
% 2.35/1.27  #Sup     : 143
% 2.35/1.27  #Fact    : 0
% 2.35/1.27  #Define  : 0
% 2.35/1.27  #Split   : 0
% 2.35/1.27  #Chain   : 0
% 2.35/1.27  #Close   : 0
% 2.35/1.27  
% 2.35/1.27  Ordering : KBO
% 2.35/1.27  
% 2.35/1.27  Simplification rules
% 2.35/1.27  ----------------------
% 2.35/1.27  #Subsume      : 4
% 2.35/1.27  #Demod        : 70
% 2.35/1.27  #Tautology    : 80
% 2.35/1.27  #SimpNegUnit  : 1
% 2.35/1.27  #BackRed      : 7
% 2.35/1.27  
% 2.35/1.27  #Partial instantiations: 0
% 2.35/1.27  #Strategies tried      : 1
% 2.35/1.27  
% 2.35/1.27  Timing (in seconds)
% 2.35/1.27  ----------------------
% 2.35/1.27  Preprocessing        : 0.34
% 2.35/1.27  Parsing              : 0.17
% 2.35/1.27  CNF conversion       : 0.02
% 2.35/1.27  Main loop            : 0.29
% 2.35/1.27  Inferencing          : 0.11
% 2.35/1.27  Reduction            : 0.10
% 2.35/1.27  Demodulation         : 0.08
% 2.35/1.27  BG Simplification    : 0.02
% 2.35/1.27  Subsumption          : 0.05
% 2.35/1.27  Abstraction          : 0.01
% 2.35/1.27  MUC search           : 0.00
% 2.35/1.27  Cooper               : 0.00
% 2.35/1.27  Total                : 0.66
% 2.35/1.27  Index Insertion      : 0.00
% 2.35/1.27  Index Deletion       : 0.00
% 2.35/1.28  Index Matching       : 0.00
% 2.35/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
