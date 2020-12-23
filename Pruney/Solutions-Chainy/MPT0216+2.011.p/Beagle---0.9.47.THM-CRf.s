%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  74 expanded)
%              Number of equality atoms :   34 (  60 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_30,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_55,plain,(
    ! [B_39,A_40,C_41] :
      ( B_39 = A_40
      | k2_tarski(B_39,C_41) != k1_tarski(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    ! [A_40] :
      ( A_40 = '#skF_2'
      | k1_tarski(A_40) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_55])).

tff(c_69,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_61])).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_28])).

tff(c_72,plain,(
    k2_tarski('#skF_1','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_30])).

tff(c_20,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_319,plain,(
    ! [A_74,B_75,C_76,D_77] : k2_xboole_0(k2_tarski(A_74,B_75),k2_tarski(C_76,D_77)) = k2_enumset1(A_74,B_75,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_353,plain,(
    ! [A_22,C_76,D_77] : k2_xboole_0(k1_tarski(A_22),k2_tarski(C_76,D_77)) = k2_enumset1(A_22,A_22,C_76,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_319])).

tff(c_363,plain,(
    ! [A_22,C_76,D_77] : k2_xboole_0(k1_tarski(A_22),k2_tarski(C_76,D_77)) = k1_enumset1(A_22,C_76,D_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_353])).

tff(c_121,plain,(
    ! [B_51,C_52,A_53] : k1_enumset1(B_51,C_52,A_53) = k1_enumset1(A_53,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_141,plain,(
    ! [A_53,C_52] : k1_enumset1(A_53,C_52,C_52) = k2_tarski(C_52,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_20])).

tff(c_430,plain,(
    ! [A_83,C_84,D_85] : k2_xboole_0(k1_tarski(A_83),k2_tarski(C_84,D_85)) = k1_enumset1(A_83,C_84,D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_353])).

tff(c_457,plain,(
    ! [A_83,A_22] : k2_xboole_0(k1_tarski(A_83),k1_tarski(A_22)) = k1_enumset1(A_83,A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_430])).

tff(c_610,plain,(
    ! [A_98,A_99] : k2_xboole_0(k1_tarski(A_98),k1_tarski(A_99)) = k2_tarski(A_99,A_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_457])).

tff(c_99,plain,(
    ! [A_49,B_50] : k4_xboole_0(k2_xboole_0(A_49,B_50),B_50) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_49,B_50] : r1_tarski(k4_xboole_0(A_49,B_50),k2_xboole_0(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_8])).

tff(c_271,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,k2_xboole_0(B_67,C_68))
      | ~ r1_tarski(k4_xboole_0(A_66,B_67),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_286,plain,(
    ! [A_49,B_50] : r1_tarski(A_49,k2_xboole_0(B_50,k2_xboole_0(A_49,B_50))) ),
    inference(resolution,[status(thm)],[c_111,c_271])).

tff(c_616,plain,(
    ! [A_98,A_99] : r1_tarski(k1_tarski(A_98),k2_xboole_0(k1_tarski(A_99),k2_tarski(A_99,A_98))) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_286])).

tff(c_647,plain,(
    ! [A_100,A_101] : r1_tarski(k1_tarski(A_100),k2_tarski(A_101,A_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_363,c_616])).

tff(c_650,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_647])).

tff(c_24,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | ~ r1_tarski(k1_tarski(A_28),k1_tarski(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_657,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_650,c_24])).

tff(c_661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.31  
% 2.16/1.32  tff(f_66, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 2.16/1.32  tff(f_61, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.16/1.32  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.16/1.32  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.16/1.32  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.16/1.32  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.16/1.32  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 2.16/1.32  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.16/1.32  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.16/1.32  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.16/1.32  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.16/1.32  tff(c_30, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.32  tff(c_55, plain, (![B_39, A_40, C_41]: (B_39=A_40 | k2_tarski(B_39, C_41)!=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.32  tff(c_61, plain, (![A_40]: (A_40='#skF_2' | k1_tarski(A_40)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_55])).
% 2.16/1.32  tff(c_69, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_61])).
% 2.16/1.32  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.32  tff(c_73, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_28])).
% 2.16/1.32  tff(c_72, plain, (k2_tarski('#skF_1', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_30])).
% 2.16/1.32  tff(c_20, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.32  tff(c_22, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.32  tff(c_18, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.32  tff(c_319, plain, (![A_74, B_75, C_76, D_77]: (k2_xboole_0(k2_tarski(A_74, B_75), k2_tarski(C_76, D_77))=k2_enumset1(A_74, B_75, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.32  tff(c_353, plain, (![A_22, C_76, D_77]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(C_76, D_77))=k2_enumset1(A_22, A_22, C_76, D_77))), inference(superposition, [status(thm), theory('equality')], [c_18, c_319])).
% 2.16/1.32  tff(c_363, plain, (![A_22, C_76, D_77]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(C_76, D_77))=k1_enumset1(A_22, C_76, D_77))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_353])).
% 2.16/1.32  tff(c_121, plain, (![B_51, C_52, A_53]: (k1_enumset1(B_51, C_52, A_53)=k1_enumset1(A_53, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.32  tff(c_141, plain, (![A_53, C_52]: (k1_enumset1(A_53, C_52, C_52)=k2_tarski(C_52, A_53))), inference(superposition, [status(thm), theory('equality')], [c_121, c_20])).
% 2.16/1.32  tff(c_430, plain, (![A_83, C_84, D_85]: (k2_xboole_0(k1_tarski(A_83), k2_tarski(C_84, D_85))=k1_enumset1(A_83, C_84, D_85))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_353])).
% 2.16/1.32  tff(c_457, plain, (![A_83, A_22]: (k2_xboole_0(k1_tarski(A_83), k1_tarski(A_22))=k1_enumset1(A_83, A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_18, c_430])).
% 2.16/1.32  tff(c_610, plain, (![A_98, A_99]: (k2_xboole_0(k1_tarski(A_98), k1_tarski(A_99))=k2_tarski(A_99, A_98))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_457])).
% 2.16/1.32  tff(c_99, plain, (![A_49, B_50]: (k4_xboole_0(k2_xboole_0(A_49, B_50), B_50)=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.32  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.32  tff(c_111, plain, (![A_49, B_50]: (r1_tarski(k4_xboole_0(A_49, B_50), k2_xboole_0(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_8])).
% 2.16/1.32  tff(c_271, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, k2_xboole_0(B_67, C_68)) | ~r1_tarski(k4_xboole_0(A_66, B_67), C_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.32  tff(c_286, plain, (![A_49, B_50]: (r1_tarski(A_49, k2_xboole_0(B_50, k2_xboole_0(A_49, B_50))))), inference(resolution, [status(thm)], [c_111, c_271])).
% 2.16/1.32  tff(c_616, plain, (![A_98, A_99]: (r1_tarski(k1_tarski(A_98), k2_xboole_0(k1_tarski(A_99), k2_tarski(A_99, A_98))))), inference(superposition, [status(thm), theory('equality')], [c_610, c_286])).
% 2.16/1.32  tff(c_647, plain, (![A_100, A_101]: (r1_tarski(k1_tarski(A_100), k2_tarski(A_101, A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_363, c_616])).
% 2.16/1.32  tff(c_650, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_647])).
% 2.16/1.32  tff(c_24, plain, (![B_29, A_28]: (B_29=A_28 | ~r1_tarski(k1_tarski(A_28), k1_tarski(B_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.32  tff(c_657, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_650, c_24])).
% 2.16/1.32  tff(c_661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_657])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 3
% 2.16/1.32  #Sup     : 150
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 0
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 6
% 2.16/1.32  #Demod        : 78
% 2.16/1.32  #Tautology    : 89
% 2.16/1.32  #SimpNegUnit  : 1
% 2.16/1.32  #BackRed      : 3
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.32  Preprocessing        : 0.29
% 2.16/1.32  Parsing              : 0.15
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.29
% 2.16/1.32  Inferencing          : 0.11
% 2.16/1.32  Reduction            : 0.10
% 2.16/1.32  Demodulation         : 0.08
% 2.16/1.32  BG Simplification    : 0.01
% 2.16/1.32  Subsumption          : 0.04
% 2.16/1.32  Abstraction          : 0.01
% 2.16/1.32  MUC search           : 0.00
% 2.16/1.32  Cooper               : 0.00
% 2.16/1.32  Total                : 0.60
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
