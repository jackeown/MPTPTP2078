%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:45 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  66 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_34,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57,plain,(
    ! [B_38,A_39,C_40] :
      ( B_38 = A_39
      | k2_tarski(B_38,C_40) != k1_tarski(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [A_39] :
      ( A_39 = '#skF_2'
      | k1_tarski(A_39) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_57])).

tff(c_71,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_63])).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_32])).

tff(c_74,plain,(
    k2_tarski('#skF_1','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_34])).

tff(c_8,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_353,plain,(
    ! [A_70,B_71,C_72] : k2_xboole_0(k1_tarski(A_70),k2_tarski(B_71,C_72)) = k1_enumset1(A_70,B_71,C_72) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_368,plain,(
    ! [A_70,A_19] : k2_xboole_0(k1_tarski(A_70),k1_tarski(A_19)) = k1_enumset1(A_70,A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_353])).

tff(c_372,plain,(
    ! [A_70,A_19] : k1_enumset1(A_70,A_19,A_19) = k2_tarski(A_70,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_368])).

tff(c_216,plain,(
    ! [B_62,C_63,D_64,A_65] : k2_enumset1(B_62,C_63,D_64,A_65) = k2_enumset1(A_65,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_744,plain,(
    ! [B_92,C_93,D_94] : k2_enumset1(B_92,C_93,D_94,B_92) = k1_enumset1(B_92,C_93,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_16])).

tff(c_236,plain,(
    ! [A_65,C_63,D_64] : k2_enumset1(A_65,C_63,C_63,D_64) = k1_enumset1(C_63,D_64,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_16])).

tff(c_751,plain,(
    ! [D_94,B_92] : k1_enumset1(D_94,B_92,B_92) = k1_enumset1(B_92,D_94,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_236])).

tff(c_868,plain,(
    ! [D_98,B_99] : k2_tarski(D_98,B_99) = k2_tarski(B_99,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_372,c_751])).

tff(c_30,plain,(
    ! [B_31,A_30,C_32] :
      ( B_31 = A_30
      | k2_tarski(B_31,C_32) != k1_tarski(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_971,plain,(
    ! [D_102,A_103,B_104] :
      ( D_102 = A_103
      | k2_tarski(B_104,D_102) != k1_tarski(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_30])).

tff(c_980,plain,(
    ! [A_103] :
      ( A_103 = '#skF_3'
      | k1_tarski(A_103) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_971])).

tff(c_986,plain,(
    '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_980])).

tff(c_988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.40  
% 2.46/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.40  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.46/1.40  
% 2.46/1.40  %Foreground sorts:
% 2.46/1.40  
% 2.46/1.40  
% 2.46/1.40  %Background operators:
% 2.46/1.40  
% 2.46/1.40  
% 2.46/1.40  %Foreground operators:
% 2.46/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.40  
% 2.46/1.41  tff(f_72, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 2.46/1.41  tff(f_67, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.46/1.41  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.46/1.41  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.41  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.46/1.41  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 2.46/1.41  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.46/1.41  tff(c_34, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.41  tff(c_57, plain, (![B_38, A_39, C_40]: (B_38=A_39 | k2_tarski(B_38, C_40)!=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.41  tff(c_63, plain, (![A_39]: (A_39='#skF_2' | k1_tarski(A_39)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_57])).
% 2.46/1.41  tff(c_71, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_63])).
% 2.46/1.41  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.41  tff(c_75, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_32])).
% 2.46/1.41  tff(c_74, plain, (k2_tarski('#skF_1', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_34])).
% 2.46/1.41  tff(c_8, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.41  tff(c_14, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.41  tff(c_353, plain, (![A_70, B_71, C_72]: (k2_xboole_0(k1_tarski(A_70), k2_tarski(B_71, C_72))=k1_enumset1(A_70, B_71, C_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.41  tff(c_368, plain, (![A_70, A_19]: (k2_xboole_0(k1_tarski(A_70), k1_tarski(A_19))=k1_enumset1(A_70, A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_14, c_353])).
% 2.46/1.41  tff(c_372, plain, (![A_70, A_19]: (k1_enumset1(A_70, A_19, A_19)=k2_tarski(A_70, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_368])).
% 2.46/1.41  tff(c_216, plain, (![B_62, C_63, D_64, A_65]: (k2_enumset1(B_62, C_63, D_64, A_65)=k2_enumset1(A_65, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.41  tff(c_16, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.41  tff(c_744, plain, (![B_92, C_93, D_94]: (k2_enumset1(B_92, C_93, D_94, B_92)=k1_enumset1(B_92, C_93, D_94))), inference(superposition, [status(thm), theory('equality')], [c_216, c_16])).
% 2.46/1.41  tff(c_236, plain, (![A_65, C_63, D_64]: (k2_enumset1(A_65, C_63, C_63, D_64)=k1_enumset1(C_63, D_64, A_65))), inference(superposition, [status(thm), theory('equality')], [c_216, c_16])).
% 2.46/1.41  tff(c_751, plain, (![D_94, B_92]: (k1_enumset1(D_94, B_92, B_92)=k1_enumset1(B_92, D_94, D_94))), inference(superposition, [status(thm), theory('equality')], [c_744, c_236])).
% 2.46/1.41  tff(c_868, plain, (![D_98, B_99]: (k2_tarski(D_98, B_99)=k2_tarski(B_99, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_372, c_751])).
% 2.46/1.41  tff(c_30, plain, (![B_31, A_30, C_32]: (B_31=A_30 | k2_tarski(B_31, C_32)!=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.41  tff(c_971, plain, (![D_102, A_103, B_104]: (D_102=A_103 | k2_tarski(B_104, D_102)!=k1_tarski(A_103))), inference(superposition, [status(thm), theory('equality')], [c_868, c_30])).
% 2.46/1.41  tff(c_980, plain, (![A_103]: (A_103='#skF_3' | k1_tarski(A_103)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_971])).
% 2.46/1.41  tff(c_986, plain, ('#skF_3'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_980])).
% 2.46/1.41  tff(c_988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_986])).
% 2.46/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.41  
% 2.46/1.41  Inference rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Ref     : 3
% 2.46/1.41  #Sup     : 226
% 2.46/1.41  #Fact    : 0
% 2.46/1.41  #Define  : 0
% 2.46/1.41  #Split   : 0
% 2.46/1.41  #Chain   : 0
% 2.46/1.41  #Close   : 0
% 2.46/1.41  
% 2.46/1.41  Ordering : KBO
% 2.46/1.41  
% 2.46/1.41  Simplification rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Subsume      : 6
% 2.46/1.41  #Demod        : 148
% 2.46/1.41  #Tautology    : 174
% 2.46/1.41  #SimpNegUnit  : 1
% 2.46/1.41  #BackRed      : 3
% 2.46/1.41  
% 2.46/1.41  #Partial instantiations: 0
% 2.46/1.41  #Strategies tried      : 1
% 2.46/1.41  
% 2.46/1.41  Timing (in seconds)
% 2.46/1.41  ----------------------
% 2.46/1.42  Preprocessing        : 0.30
% 2.46/1.42  Parsing              : 0.16
% 2.46/1.42  CNF conversion       : 0.02
% 2.46/1.42  Main loop            : 0.31
% 2.46/1.42  Inferencing          : 0.12
% 2.46/1.42  Reduction            : 0.11
% 2.71/1.42  Demodulation         : 0.09
% 2.71/1.42  BG Simplification    : 0.02
% 2.71/1.42  Subsumption          : 0.04
% 2.71/1.42  Abstraction          : 0.02
% 2.71/1.42  MUC search           : 0.00
% 2.71/1.42  Cooper               : 0.00
% 2.71/1.42  Total                : 0.64
% 2.71/1.42  Index Insertion      : 0.00
% 2.71/1.42  Index Deletion       : 0.00
% 2.71/1.42  Index Matching       : 0.00
% 2.71/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
