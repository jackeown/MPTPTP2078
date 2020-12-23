%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:24 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 103 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 105 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_205,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_259,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(resolution,[status(thm)],[c_12,c_205])).

tff(c_293,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_129,plain,(
    ! [A_40,B_41] : r1_tarski(A_40,k2_xboole_0(B_41,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_16])).

tff(c_138,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_228,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_205])).

tff(c_323,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_228])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_252,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden(A_51,B_52)
      | ~ r1_xboole_0(k1_tarski(A_51),B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_257,plain,(
    ! [A_51] : ~ r2_hidden(A_51,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_252])).

tff(c_381,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_257])).

tff(c_385,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_46])).

tff(c_272,plain,(
    ! [A_54] : k2_xboole_0(A_54,k1_xboole_0) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_2])).

tff(c_421,plain,(
    ! [A_54] : k2_xboole_0(A_54,'#skF_4') = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_272])).

tff(c_468,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_421])).

tff(c_36,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ! [D_33,A_34] : r2_hidden(D_33,k2_tarski(A_34,D_33)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_505,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_71])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:59:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.25  
% 2.15/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.15/1.26  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.26  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.15/1.26  tff(f_69, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.15/1.26  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.15/1.26  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.15/1.26  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.15/1.26  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.26  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.15/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.26  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.26  tff(c_205, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.26  tff(c_259, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, A_54)=A_54)), inference(resolution, [status(thm)], [c_12, c_205])).
% 2.15/1.26  tff(c_293, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_259])).
% 2.15/1.26  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.26  tff(c_78, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.26  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.26  tff(c_129, plain, (![A_40, B_41]: (r1_tarski(A_40, k2_xboole_0(B_41, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_16])).
% 2.15/1.26  tff(c_138, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_129])).
% 2.15/1.26  tff(c_228, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_205])).
% 2.15/1.26  tff(c_323, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_293, c_228])).
% 2.15/1.26  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.26  tff(c_252, plain, (![A_51, B_52]: (~r2_hidden(A_51, B_52) | ~r1_xboole_0(k1_tarski(A_51), B_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.26  tff(c_257, plain, (![A_51]: (~r2_hidden(A_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_252])).
% 2.15/1.26  tff(c_381, plain, (![A_51]: (~r2_hidden(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_257])).
% 2.15/1.26  tff(c_385, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_46])).
% 2.15/1.26  tff(c_272, plain, (![A_54]: (k2_xboole_0(A_54, k1_xboole_0)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_259, c_2])).
% 2.15/1.26  tff(c_421, plain, (![A_54]: (k2_xboole_0(A_54, '#skF_4')=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_323, c_272])).
% 2.15/1.26  tff(c_468, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_385, c_421])).
% 2.15/1.26  tff(c_36, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.26  tff(c_68, plain, (![D_33, A_34]: (r2_hidden(D_33, k2_tarski(A_34, D_33)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.26  tff(c_71, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_68])).
% 2.15/1.26  tff(c_505, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_468, c_71])).
% 2.15/1.26  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_505])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 113
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 0
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 3
% 2.15/1.26  #Demod        : 49
% 2.15/1.26  #Tautology    : 78
% 2.15/1.26  #SimpNegUnit  : 1
% 2.15/1.26  #BackRed      : 13
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.26  Preprocessing        : 0.30
% 2.15/1.26  Parsing              : 0.16
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.21
% 2.15/1.26  Inferencing          : 0.07
% 2.15/1.26  Reduction            : 0.08
% 2.15/1.26  Demodulation         : 0.06
% 2.15/1.26  BG Simplification    : 0.01
% 2.15/1.26  Subsumption          : 0.04
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.54
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
