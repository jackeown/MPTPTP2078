%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  48 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [B_66,A_65] : r2_hidden(B_66,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_32])).

tff(c_26,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_111,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_176,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_111])).

tff(c_66,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_182,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,A_73) = k2_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_66])).

tff(c_70,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_199,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_71])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_252,plain,
    ( k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_199,c_20])).

tff(c_255,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_252])).

tff(c_284,plain,(
    ! [D_82,B_83,A_84] :
      ( ~ r2_hidden(D_82,B_83)
      | r2_hidden(D_82,k2_xboole_0(A_84,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_296,plain,(
    ! [D_85] :
      ( ~ r2_hidden(D_85,k2_tarski('#skF_6','#skF_5'))
      | r2_hidden(D_85,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_284])).

tff(c_304,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_132,c_296])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  
% 2.24/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.35  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.24/1.35  
% 2.24/1.35  %Foreground sorts:
% 2.24/1.35  
% 2.24/1.35  
% 2.24/1.35  %Background operators:
% 2.24/1.35  
% 2.24/1.35  
% 2.24/1.35  %Foreground operators:
% 2.24/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.24/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.24/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.24/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.24/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.24/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.35  
% 2.24/1.36  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.24/1.36  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.36  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.24/1.36  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.24/1.36  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.24/1.36  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.24/1.36  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.24/1.36  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.24/1.36  tff(c_68, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.24/1.36  tff(c_126, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.24/1.36  tff(c_32, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.36  tff(c_132, plain, (![B_66, A_65]: (r2_hidden(B_66, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_32])).
% 2.24/1.36  tff(c_26, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.36  tff(c_28, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.24/1.36  tff(c_111, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.36  tff(c_176, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_28, c_111])).
% 2.24/1.36  tff(c_66, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.36  tff(c_182, plain, (![B_74, A_73]: (k2_xboole_0(B_74, A_73)=k2_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_176, c_66])).
% 2.24/1.36  tff(c_70, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.24/1.36  tff(c_71, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 2.24/1.36  tff(c_199, plain, (r1_tarski(k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_71])).
% 2.24/1.36  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.36  tff(c_252, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_199, c_20])).
% 2.24/1.36  tff(c_255, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_252])).
% 2.24/1.36  tff(c_284, plain, (![D_82, B_83, A_84]: (~r2_hidden(D_82, B_83) | r2_hidden(D_82, k2_xboole_0(A_84, B_83)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.36  tff(c_296, plain, (![D_85]: (~r2_hidden(D_85, k2_tarski('#skF_6', '#skF_5')) | r2_hidden(D_85, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_284])).
% 2.24/1.36  tff(c_304, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_132, c_296])).
% 2.24/1.36  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_304])).
% 2.24/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.36  
% 2.24/1.36  Inference rules
% 2.24/1.36  ----------------------
% 2.24/1.36  #Ref     : 0
% 2.24/1.36  #Sup     : 57
% 2.24/1.36  #Fact    : 0
% 2.24/1.36  #Define  : 0
% 2.24/1.36  #Split   : 0
% 2.24/1.36  #Chain   : 0
% 2.24/1.36  #Close   : 0
% 2.24/1.36  
% 2.24/1.36  Ordering : KBO
% 2.24/1.36  
% 2.24/1.36  Simplification rules
% 2.24/1.36  ----------------------
% 2.24/1.36  #Subsume      : 5
% 2.24/1.36  #Demod        : 23
% 2.24/1.36  #Tautology    : 41
% 2.24/1.36  #SimpNegUnit  : 1
% 2.24/1.36  #BackRed      : 2
% 2.24/1.36  
% 2.24/1.36  #Partial instantiations: 0
% 2.24/1.36  #Strategies tried      : 1
% 2.24/1.36  
% 2.24/1.36  Timing (in seconds)
% 2.24/1.36  ----------------------
% 2.24/1.36  Preprocessing        : 0.35
% 2.24/1.36  Parsing              : 0.18
% 2.24/1.36  CNF conversion       : 0.03
% 2.24/1.36  Main loop            : 0.19
% 2.24/1.36  Inferencing          : 0.05
% 2.24/1.36  Reduction            : 0.07
% 2.24/1.36  Demodulation         : 0.06
% 2.24/1.36  BG Simplification    : 0.02
% 2.24/1.36  Subsumption          : 0.04
% 2.24/1.36  Abstraction          : 0.01
% 2.24/1.36  MUC search           : 0.00
% 2.24/1.36  Cooper               : 0.00
% 2.24/1.36  Total                : 0.56
% 2.24/1.36  Index Insertion      : 0.00
% 2.24/1.36  Index Deletion       : 0.00
% 2.24/1.36  Index Matching       : 0.00
% 2.24/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
