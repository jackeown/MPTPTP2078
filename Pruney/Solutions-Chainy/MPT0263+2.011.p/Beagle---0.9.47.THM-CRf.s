%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:15 EST 2020

% Result     : Theorem 19.63s
% Output     : CNFRefutation 19.63s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  52 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_106,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_52])).

tff(c_108,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_147,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_5'(A_52,B_53),A_52)
      | k1_xboole_0 = A_52
      | k1_tarski(B_53) = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1286,plain,(
    ! [A_1366,B_1367,B_1368] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_1366,B_1367),B_1368),B_1367)
      | k3_xboole_0(A_1366,B_1367) = k1_xboole_0
      | k3_xboole_0(A_1366,B_1367) = k1_tarski(B_1368) ) ),
    inference(resolution,[status(thm)],[c_147,c_6])).

tff(c_26,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97240,plain,(
    ! [A_61749,A_61750,B_61751] :
      ( '#skF_5'(k3_xboole_0(A_61749,k1_tarski(A_61750)),B_61751) = A_61750
      | k3_xboole_0(A_61749,k1_tarski(A_61750)) = k1_xboole_0
      | k3_xboole_0(A_61749,k1_tarski(A_61750)) = k1_tarski(B_61751) ) ),
    inference(resolution,[status(thm)],[c_1286,c_26])).

tff(c_46,plain,(
    ! [A_26,B_27] :
      ( '#skF_5'(A_26,B_27) != B_27
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99250,plain,(
    ! [A_62187,B_62188] :
      ( k3_xboole_0(A_62187,k1_tarski(B_62188)) = k1_xboole_0
      | k3_xboole_0(A_62187,k1_tarski(B_62188)) = k1_tarski(B_62188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97240,c_46])).

tff(c_50,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_99364,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99250,c_53])).

tff(c_100649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_99364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:14:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.63/10.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.63/10.69  
% 19.63/10.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.63/10.69  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 19.63/10.69  
% 19.63/10.69  %Foreground sorts:
% 19.63/10.69  
% 19.63/10.69  
% 19.63/10.69  %Background operators:
% 19.63/10.69  
% 19.63/10.69  
% 19.63/10.69  %Foreground operators:
% 19.63/10.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 19.63/10.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.63/10.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.63/10.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.63/10.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.63/10.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.63/10.69  tff('#skF_7', type, '#skF_7': $i).
% 19.63/10.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.63/10.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.63/10.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.63/10.69  tff('#skF_6', type, '#skF_6': $i).
% 19.63/10.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.63/10.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 19.63/10.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.63/10.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.63/10.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.63/10.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.63/10.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.63/10.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.63/10.69  
% 19.63/10.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.63/10.70  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 19.63/10.70  tff(f_74, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 19.63/10.70  tff(f_69, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 19.63/10.70  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 19.63/10.70  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 19.63/10.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.63/10.70  tff(c_103, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.63/10.70  tff(c_52, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.63/10.70  tff(c_106, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_52])).
% 19.63/10.70  tff(c_108, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_106])).
% 19.63/10.70  tff(c_147, plain, (![A_52, B_53]: (r2_hidden('#skF_5'(A_52, B_53), A_52) | k1_xboole_0=A_52 | k1_tarski(B_53)=A_52)), inference(cnfTransformation, [status(thm)], [f_69])).
% 19.63/10.70  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.63/10.70  tff(c_1286, plain, (![A_1366, B_1367, B_1368]: (r2_hidden('#skF_5'(k3_xboole_0(A_1366, B_1367), B_1368), B_1367) | k3_xboole_0(A_1366, B_1367)=k1_xboole_0 | k3_xboole_0(A_1366, B_1367)=k1_tarski(B_1368))), inference(resolution, [status(thm)], [c_147, c_6])).
% 19.63/10.70  tff(c_26, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.63/10.70  tff(c_97240, plain, (![A_61749, A_61750, B_61751]: ('#skF_5'(k3_xboole_0(A_61749, k1_tarski(A_61750)), B_61751)=A_61750 | k3_xboole_0(A_61749, k1_tarski(A_61750))=k1_xboole_0 | k3_xboole_0(A_61749, k1_tarski(A_61750))=k1_tarski(B_61751))), inference(resolution, [status(thm)], [c_1286, c_26])).
% 19.63/10.70  tff(c_46, plain, (![A_26, B_27]: ('#skF_5'(A_26, B_27)!=B_27 | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_69])).
% 19.63/10.70  tff(c_99250, plain, (![A_62187, B_62188]: (k3_xboole_0(A_62187, k1_tarski(B_62188))=k1_xboole_0 | k3_xboole_0(A_62187, k1_tarski(B_62188))=k1_tarski(B_62188))), inference(superposition, [status(thm), theory('equality')], [c_97240, c_46])).
% 19.63/10.70  tff(c_50, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.63/10.70  tff(c_53, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 19.63/10.70  tff(c_99364, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99250, c_53])).
% 19.63/10.70  tff(c_100649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_99364])).
% 19.63/10.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.63/10.70  
% 19.63/10.70  Inference rules
% 19.63/10.70  ----------------------
% 19.63/10.70  #Ref     : 0
% 19.63/10.70  #Sup     : 14317
% 19.63/10.70  #Fact    : 18
% 19.63/10.70  #Define  : 0
% 19.63/10.70  #Split   : 6
% 19.63/10.70  #Chain   : 0
% 19.63/10.70  #Close   : 0
% 19.63/10.70  
% 19.63/10.70  Ordering : KBO
% 19.63/10.70  
% 19.63/10.70  Simplification rules
% 19.63/10.70  ----------------------
% 19.63/10.70  #Subsume      : 1064
% 19.63/10.70  #Demod        : 3233
% 19.63/10.70  #Tautology    : 1167
% 19.63/10.70  #SimpNegUnit  : 219
% 19.63/10.70  #BackRed      : 16
% 19.63/10.70  
% 19.63/10.70  #Partial instantiations: 30044
% 19.63/10.70  #Strategies tried      : 1
% 19.63/10.70  
% 19.63/10.70  Timing (in seconds)
% 19.63/10.70  ----------------------
% 19.63/10.71  Preprocessing        : 0.30
% 19.63/10.71  Parsing              : 0.15
% 19.63/10.71  CNF conversion       : 0.02
% 19.63/10.71  Main loop            : 9.64
% 19.63/10.71  Inferencing          : 2.72
% 19.63/10.71  Reduction            : 2.03
% 19.63/10.71  Demodulation         : 1.53
% 19.63/10.71  BG Simplification    : 0.54
% 19.63/10.71  Subsumption          : 3.99
% 19.63/10.71  Abstraction          : 0.75
% 19.63/10.71  MUC search           : 0.00
% 19.63/10.71  Cooper               : 0.00
% 19.63/10.71  Total                : 9.97
% 19.63/10.71  Index Insertion      : 0.00
% 19.63/10.71  Index Deletion       : 0.00
% 19.63/10.71  Index Matching       : 0.00
% 19.63/10.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
