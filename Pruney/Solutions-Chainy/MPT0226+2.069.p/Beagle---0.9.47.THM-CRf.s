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
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  51 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    ! [D_26,B_27] : r2_hidden(D_26,k2_tarski(D_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_64])).

tff(c_54,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_79,c_26])).

tff(c_113,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_109])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k1_tarski('#skF_5'))
      | r2_hidden(D_52,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_6])).

tff(c_138,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_67,c_133])).

tff(c_139,plain,(
    ! [D_53,B_54,A_55] :
      ( D_53 = B_54
      | D_53 = A_55
      | ~ r2_hidden(D_53,k2_tarski(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    ! [D_59,A_60] :
      ( D_59 = A_60
      | D_59 = A_60
      | ~ r2_hidden(D_59,k1_tarski(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_139])).

tff(c_168,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_138,c_165])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.35  
% 2.12/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.35  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.12/1.35  
% 2.12/1.35  %Foreground sorts:
% 2.12/1.35  
% 2.12/1.35  
% 2.12/1.35  %Background operators:
% 2.12/1.35  
% 2.12/1.35  
% 2.12/1.35  %Foreground operators:
% 2.12/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.12/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.12/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.12/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.12/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.35  
% 2.12/1.36  tff(f_64, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.12/1.36  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.36  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.12/1.36  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.12/1.36  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.12/1.36  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.12/1.36  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.36  tff(c_46, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.36  tff(c_64, plain, (![D_26, B_27]: (r2_hidden(D_26, k2_tarski(D_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.36  tff(c_67, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_64])).
% 2.12/1.36  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.36  tff(c_79, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.36  tff(c_26, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.36  tff(c_109, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_26])).
% 2.12/1.36  tff(c_113, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_54, c_109])).
% 2.12/1.36  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.36  tff(c_133, plain, (![D_52]: (~r2_hidden(D_52, k1_tarski('#skF_5')) | r2_hidden(D_52, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_6])).
% 2.12/1.36  tff(c_138, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_67, c_133])).
% 2.12/1.36  tff(c_139, plain, (![D_53, B_54, A_55]: (D_53=B_54 | D_53=A_55 | ~r2_hidden(D_53, k2_tarski(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.36  tff(c_165, plain, (![D_59, A_60]: (D_59=A_60 | D_59=A_60 | ~r2_hidden(D_59, k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_139])).
% 2.12/1.36  tff(c_168, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_138, c_165])).
% 2.12/1.36  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_168])).
% 2.12/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.36  
% 2.12/1.36  Inference rules
% 2.12/1.36  ----------------------
% 2.12/1.36  #Ref     : 0
% 2.12/1.36  #Sup     : 28
% 2.12/1.36  #Fact    : 0
% 2.12/1.36  #Define  : 0
% 2.12/1.36  #Split   : 0
% 2.12/1.36  #Chain   : 0
% 2.12/1.36  #Close   : 0
% 2.12/1.36  
% 2.12/1.36  Ordering : KBO
% 2.12/1.36  
% 2.12/1.36  Simplification rules
% 2.12/1.36  ----------------------
% 2.12/1.36  #Subsume      : 0
% 2.12/1.36  #Demod        : 1
% 2.12/1.36  #Tautology    : 20
% 2.12/1.36  #SimpNegUnit  : 1
% 2.12/1.36  #BackRed      : 0
% 2.12/1.36  
% 2.12/1.36  #Partial instantiations: 0
% 2.12/1.36  #Strategies tried      : 1
% 2.12/1.36  
% 2.12/1.36  Timing (in seconds)
% 2.12/1.36  ----------------------
% 2.12/1.37  Preprocessing        : 0.33
% 2.12/1.37  Parsing              : 0.17
% 2.12/1.37  CNF conversion       : 0.03
% 2.12/1.37  Main loop            : 0.14
% 2.12/1.37  Inferencing          : 0.05
% 2.12/1.37  Reduction            : 0.05
% 2.12/1.37  Demodulation         : 0.03
% 2.12/1.37  BG Simplification    : 0.01
% 2.12/1.37  Subsumption          : 0.03
% 2.12/1.37  Abstraction          : 0.01
% 2.12/1.37  MUC search           : 0.00
% 2.12/1.37  Cooper               : 0.00
% 2.12/1.37  Total                : 0.50
% 2.12/1.37  Index Insertion      : 0.00
% 2.12/1.37  Index Deletion       : 0.00
% 2.12/1.37  Index Matching       : 0.00
% 2.12/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
