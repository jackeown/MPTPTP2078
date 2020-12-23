%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:28 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  79 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_261,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_243])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_273,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_261,c_4])).

tff(c_275,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_273])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_10])).

tff(c_339,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ r1_xboole_0(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_344,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_4') ),
    inference(resolution,[status(thm)],[c_282,c_339])).

tff(c_133,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_83])).

tff(c_402,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_133])).

tff(c_111,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_6])).

tff(c_277,plain,(
    ! [A_36] : k2_xboole_0('#skF_4',A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_111])).

tff(c_406,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_277])).

tff(c_34,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [D_27,B_28] : r2_hidden(D_27,k2_tarski(D_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_65])).

tff(c_431,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_68])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:21:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.03/1.27  
% 2.03/1.27  %Foreground sorts:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Background operators:
% 2.03/1.27  
% 2.03/1.27  
% 2.03/1.27  %Foreground operators:
% 2.03/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.27  
% 2.03/1.28  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.03/1.28  tff(f_63, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.03/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.03/1.28  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.03/1.28  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.03/1.28  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.03/1.28  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.03/1.28  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.28  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.03/1.28  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.28  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.28  tff(c_83, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.28  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.28  tff(c_243, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 2.03/1.28  tff(c_261, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_243])).
% 2.03/1.28  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.28  tff(c_273, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_261, c_4])).
% 2.03/1.28  tff(c_275, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_273])).
% 2.03/1.28  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.28  tff(c_282, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_10])).
% 2.03/1.28  tff(c_339, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~r1_xboole_0(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.28  tff(c_344, plain, (![A_46]: (~r2_hidden(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_282, c_339])).
% 2.03/1.28  tff(c_133, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_83])).
% 2.03/1.28  tff(c_402, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_133])).
% 2.03/1.28  tff(c_111, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_83, c_6])).
% 2.03/1.28  tff(c_277, plain, (![A_36]: (k2_xboole_0('#skF_4', A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_111])).
% 2.03/1.28  tff(c_406, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_402, c_277])).
% 2.03/1.28  tff(c_34, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.28  tff(c_65, plain, (![D_27, B_28]: (r2_hidden(D_27, k2_tarski(D_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.28  tff(c_68, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_65])).
% 2.03/1.28  tff(c_431, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_406, c_68])).
% 2.03/1.28  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_431])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 93
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 0
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 0
% 2.03/1.28  #Demod        : 41
% 2.03/1.28  #Tautology    : 69
% 2.03/1.28  #SimpNegUnit  : 1
% 2.03/1.28  #BackRed      : 9
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.03/1.28  Preprocessing        : 0.31
% 2.03/1.28  Parsing              : 0.16
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.21
% 2.03/1.28  Inferencing          : 0.07
% 2.03/1.28  Reduction            : 0.08
% 2.03/1.28  Demodulation         : 0.06
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.29  Subsumption          : 0.04
% 2.03/1.29  Abstraction          : 0.01
% 2.03/1.29  MUC search           : 0.00
% 2.03/1.29  Cooper               : 0.00
% 2.03/1.29  Total                : 0.55
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
