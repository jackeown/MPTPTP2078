%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   47 (  75 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  68 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k2_enumset1(A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_327,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_xboole_0(k2_tarski(A_43,B_44),k2_tarski(C_45,D_46)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_368,plain,(
    ! [A_10,C_45,D_46] : k2_xboole_0(k1_tarski(A_10),k2_tarski(C_45,D_46)) = k2_enumset1(A_10,A_10,C_45,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_327])).

tff(c_374,plain,(
    ! [A_10,C_45,D_46] : k2_xboole_0(k1_tarski(A_10),k2_tarski(C_45,D_46)) = k1_enumset1(A_10,C_45,D_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_368])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [B_36,A_37] : k3_tarski(k2_tarski(B_36,A_37)) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_216,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_27,B_28] :
      ( k1_xboole_0 = A_27
      | k2_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_90,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_20])).

tff(c_237,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_90])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_237])).

tff(c_18,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),B_19) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_540,plain,(
    ! [A_56,B_57] : k2_xboole_0(k1_tarski(A_56),B_57) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_18])).

tff(c_563,plain,(
    ! [A_58,C_59,D_60] : k1_enumset1(A_58,C_59,D_60) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_540])).

tff(c_565,plain,(
    ! [A_11,B_12] : k2_tarski(A_11,B_12) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_563])).

tff(c_315,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_89])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.26  
% 2.24/1.26  %Foreground sorts:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Background operators:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Foreground operators:
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.26  
% 2.24/1.27  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.27  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.24/1.27  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.27  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.24/1.27  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.24/1.27  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.24/1.27  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.24/1.27  tff(f_50, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.24/1.27  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.24/1.27  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.24/1.27  tff(c_12, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.27  tff(c_14, plain, (![A_13, B_14, C_15]: (k2_enumset1(A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.27  tff(c_10, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.27  tff(c_327, plain, (![A_43, B_44, C_45, D_46]: (k2_xboole_0(k2_tarski(A_43, B_44), k2_tarski(C_45, D_46))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.27  tff(c_368, plain, (![A_10, C_45, D_46]: (k2_xboole_0(k1_tarski(A_10), k2_tarski(C_45, D_46))=k2_enumset1(A_10, A_10, C_45, D_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_327])).
% 2.24/1.27  tff(c_374, plain, (![A_10, C_45, D_46]: (k2_xboole_0(k1_tarski(A_10), k2_tarski(C_45, D_46))=k1_enumset1(A_10, C_45, D_46))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_368])).
% 2.24/1.27  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.27  tff(c_16, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.27  tff(c_6, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.27  tff(c_104, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.27  tff(c_171, plain, (![B_36, A_37]: (k3_tarski(k2_tarski(B_36, A_37))=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_6, c_104])).
% 2.24/1.27  tff(c_216, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_16, c_171])).
% 2.24/1.27  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.27  tff(c_82, plain, (![A_27, B_28]: (k1_xboole_0=A_27 | k2_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.27  tff(c_89, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_82])).
% 2.24/1.27  tff(c_90, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89, c_20])).
% 2.24/1.27  tff(c_237, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_216, c_90])).
% 2.24/1.27  tff(c_299, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_237])).
% 2.24/1.27  tff(c_18, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.27  tff(c_540, plain, (![A_56, B_57]: (k2_xboole_0(k1_tarski(A_56), B_57)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_18])).
% 2.24/1.27  tff(c_563, plain, (![A_58, C_59, D_60]: (k1_enumset1(A_58, C_59, D_60)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_374, c_540])).
% 2.24/1.27  tff(c_565, plain, (![A_11, B_12]: (k2_tarski(A_11, B_12)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_563])).
% 2.24/1.27  tff(c_315, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_89])).
% 2.24/1.27  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_315])).
% 2.24/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  Inference rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Ref     : 0
% 2.24/1.27  #Sup     : 143
% 2.24/1.27  #Fact    : 0
% 2.24/1.27  #Define  : 0
% 2.24/1.27  #Split   : 1
% 2.24/1.27  #Chain   : 0
% 2.24/1.27  #Close   : 0
% 2.24/1.27  
% 2.24/1.27  Ordering : KBO
% 2.24/1.27  
% 2.24/1.27  Simplification rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Subsume      : 10
% 2.24/1.27  #Demod        : 54
% 2.24/1.27  #Tautology    : 90
% 2.24/1.27  #SimpNegUnit  : 1
% 2.24/1.27  #BackRed      : 13
% 2.24/1.27  
% 2.24/1.27  #Partial instantiations: 0
% 2.24/1.27  #Strategies tried      : 1
% 2.24/1.27  
% 2.24/1.27  Timing (in seconds)
% 2.24/1.27  ----------------------
% 2.24/1.27  Preprocessing        : 0.27
% 2.24/1.27  Parsing              : 0.14
% 2.24/1.27  CNF conversion       : 0.02
% 2.24/1.27  Main loop            : 0.25
% 2.24/1.27  Inferencing          : 0.09
% 2.24/1.27  Reduction            : 0.09
% 2.24/1.27  Demodulation         : 0.07
% 2.24/1.27  BG Simplification    : 0.01
% 2.24/1.27  Subsumption          : 0.04
% 2.24/1.28  Abstraction          : 0.01
% 2.24/1.28  MUC search           : 0.00
% 2.24/1.28  Cooper               : 0.00
% 2.24/1.28  Total                : 0.54
% 2.24/1.28  Index Insertion      : 0.00
% 2.24/1.28  Index Deletion       : 0.00
% 2.24/1.28  Index Matching       : 0.00
% 2.24/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
