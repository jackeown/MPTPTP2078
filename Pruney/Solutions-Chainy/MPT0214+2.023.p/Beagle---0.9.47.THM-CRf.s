%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:32 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  73 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_72,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_161,plain,(
    ! [B_65,A_66] :
      ( k1_tarski(B_65) = A_66
      | k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_tarski(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_173,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_8')
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_161])).

tff(c_176,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_50,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_50])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_143,plain,(
    ! [D_54,B_55,A_56] :
      ( ~ r2_hidden(D_54,B_55)
      | ~ r2_hidden(D_54,k4_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [D_54,A_9] :
      ( ~ r2_hidden(D_54,k1_xboole_0)
      | ~ r2_hidden(D_54,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_205,plain,(
    ! [A_9] : ~ r2_hidden('#skF_7',A_9) ),
    inference(resolution,[status(thm)],[c_194,c_146])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_194])).

tff(c_221,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_241,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_50])).

tff(c_48,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_253,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_241,c_48])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.05/1.27  
% 2.05/1.27  %Foreground sorts:
% 2.05/1.27  
% 2.05/1.27  
% 2.05/1.27  %Background operators:
% 2.05/1.27  
% 2.05/1.27  
% 2.05/1.27  %Foreground operators:
% 2.05/1.27  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.05/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.05/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.05/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.05/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.05/1.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.05/1.27  
% 2.05/1.27  tff(f_78, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.05/1.27  tff(f_73, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.05/1.27  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.05/1.27  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.05/1.27  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.05/1.27  tff(c_72, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.05/1.27  tff(c_74, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.05/1.27  tff(c_161, plain, (![B_65, A_66]: (k1_tarski(B_65)=A_66 | k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.05/1.27  tff(c_173, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8') | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_161])).
% 2.05/1.27  tff(c_176, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_173])).
% 2.05/1.27  tff(c_50, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.27  tff(c_194, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_176, c_50])).
% 2.05/1.27  tff(c_22, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.27  tff(c_143, plain, (![D_54, B_55, A_56]: (~r2_hidden(D_54, B_55) | ~r2_hidden(D_54, k4_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.27  tff(c_146, plain, (![D_54, A_9]: (~r2_hidden(D_54, k1_xboole_0) | ~r2_hidden(D_54, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_143])).
% 2.05/1.27  tff(c_205, plain, (![A_9]: (~r2_hidden('#skF_7', A_9))), inference(resolution, [status(thm)], [c_194, c_146])).
% 2.05/1.27  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_194])).
% 2.05/1.27  tff(c_221, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_173])).
% 2.05/1.27  tff(c_241, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_50])).
% 2.05/1.27  tff(c_48, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.27  tff(c_253, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_241, c_48])).
% 2.05/1.27  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_253])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 42
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 1
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 1
% 2.05/1.27  #Demod        : 18
% 2.05/1.27  #Tautology    : 31
% 2.05/1.27  #SimpNegUnit  : 2
% 2.05/1.27  #BackRed      : 4
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.28  Preprocessing        : 0.32
% 2.05/1.28  Parsing              : 0.15
% 2.05/1.28  CNF conversion       : 0.03
% 2.05/1.28  Main loop            : 0.19
% 2.05/1.28  Inferencing          : 0.06
% 2.05/1.28  Reduction            : 0.06
% 2.05/1.28  Demodulation         : 0.05
% 2.05/1.28  BG Simplification    : 0.02
% 2.05/1.28  Subsumption          : 0.04
% 2.05/1.28  Abstraction          : 0.01
% 2.05/1.28  MUC search           : 0.00
% 2.05/1.28  Cooper               : 0.00
% 2.05/1.28  Total                : 0.53
% 2.05/1.28  Index Insertion      : 0.00
% 2.05/1.28  Index Deletion       : 0.00
% 2.05/1.28  Index Matching       : 0.00
% 2.05/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
