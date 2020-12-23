%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  54 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_54,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_156,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_283,plain,(
    ! [A_70,B_71] :
      ( k2_xboole_0(k1_tarski(A_70),B_71) = B_71
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_52,c_156])).

tff(c_40,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1960,plain,(
    ! [A_152,B_153] :
      ( k3_xboole_0(k1_tarski(A_152),B_153) = k1_tarski(A_152)
      | ~ r2_hidden(A_152,B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_40])).

tff(c_2099,plain,(
    ! [A_157,A_158] :
      ( k3_xboole_0(A_157,k1_tarski(A_158)) = k1_tarski(A_158)
      | ~ r2_hidden(A_158,A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1960])).

tff(c_58,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_168,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_156])).

tff(c_185,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_40])).

tff(c_482,plain,(
    ! [A_86,B_87,C_88] : k3_xboole_0(k3_xboole_0(A_86,B_87),C_88) = k3_xboole_0(A_86,k3_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_972,plain,(
    ! [C_105] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_105)) = k3_xboole_0('#skF_4',C_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_482])).

tff(c_1033,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_972])).

tff(c_2129,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2099,c_1033])).

tff(c_2216,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2129])).

tff(c_2218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.65  
% 3.98/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.65  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.98/1.65  
% 3.98/1.65  %Foreground sorts:
% 3.98/1.65  
% 3.98/1.65  
% 3.98/1.65  %Background operators:
% 3.98/1.65  
% 3.98/1.65  
% 3.98/1.65  %Foreground operators:
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.98/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.98/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.98/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.98/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.98/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.98/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.98/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.98/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.65  
% 3.98/1.66  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 3.98/1.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.98/1.66  tff(f_72, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.98/1.66  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.98/1.66  tff(f_60, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.98/1.66  tff(f_58, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.98/1.66  tff(c_54, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.98/1.66  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.98/1.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.66  tff(c_52, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.98/1.66  tff(c_156, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.98/1.66  tff(c_283, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)=B_71 | ~r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_52, c_156])).
% 3.98/1.66  tff(c_40, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k2_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.98/1.66  tff(c_1960, plain, (![A_152, B_153]: (k3_xboole_0(k1_tarski(A_152), B_153)=k1_tarski(A_152) | ~r2_hidden(A_152, B_153))), inference(superposition, [status(thm), theory('equality')], [c_283, c_40])).
% 3.98/1.66  tff(c_2099, plain, (![A_157, A_158]: (k3_xboole_0(A_157, k1_tarski(A_158))=k1_tarski(A_158) | ~r2_hidden(A_158, A_157))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1960])).
% 3.98/1.66  tff(c_58, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.98/1.66  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.98/1.66  tff(c_168, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_156])).
% 3.98/1.66  tff(c_185, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_168, c_40])).
% 3.98/1.66  tff(c_482, plain, (![A_86, B_87, C_88]: (k3_xboole_0(k3_xboole_0(A_86, B_87), C_88)=k3_xboole_0(A_86, k3_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.66  tff(c_972, plain, (![C_105]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_105))=k3_xboole_0('#skF_4', C_105))), inference(superposition, [status(thm), theory('equality')], [c_185, c_482])).
% 3.98/1.66  tff(c_1033, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_58, c_972])).
% 3.98/1.66  tff(c_2129, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2099, c_1033])).
% 3.98/1.66  tff(c_2216, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2129])).
% 3.98/1.66  tff(c_2218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2216])).
% 3.98/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.66  
% 3.98/1.66  Inference rules
% 3.98/1.66  ----------------------
% 3.98/1.66  #Ref     : 0
% 3.98/1.66  #Sup     : 547
% 3.98/1.66  #Fact    : 0
% 3.98/1.66  #Define  : 0
% 3.98/1.66  #Split   : 1
% 3.98/1.66  #Chain   : 0
% 3.98/1.66  #Close   : 0
% 3.98/1.66  
% 3.98/1.66  Ordering : KBO
% 3.98/1.66  
% 3.98/1.66  Simplification rules
% 3.98/1.66  ----------------------
% 3.98/1.66  #Subsume      : 67
% 3.98/1.66  #Demod        : 269
% 3.98/1.66  #Tautology    : 220
% 3.98/1.66  #SimpNegUnit  : 1
% 3.98/1.66  #BackRed      : 1
% 3.98/1.66  
% 3.98/1.66  #Partial instantiations: 0
% 3.98/1.66  #Strategies tried      : 1
% 3.98/1.66  
% 3.98/1.66  Timing (in seconds)
% 3.98/1.66  ----------------------
% 3.98/1.67  Preprocessing        : 0.33
% 3.98/1.67  Parsing              : 0.16
% 3.98/1.67  CNF conversion       : 0.02
% 3.98/1.67  Main loop            : 0.59
% 3.98/1.67  Inferencing          : 0.19
% 3.98/1.67  Reduction            : 0.23
% 3.98/1.67  Demodulation         : 0.18
% 3.98/1.67  BG Simplification    : 0.03
% 3.98/1.67  Subsumption          : 0.11
% 3.98/1.67  Abstraction          : 0.03
% 3.98/1.67  MUC search           : 0.00
% 3.98/1.67  Cooper               : 0.00
% 3.98/1.67  Total                : 0.95
% 3.98/1.67  Index Insertion      : 0.00
% 3.98/1.67  Index Deletion       : 0.00
% 3.98/1.67  Index Matching       : 0.00
% 3.98/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
