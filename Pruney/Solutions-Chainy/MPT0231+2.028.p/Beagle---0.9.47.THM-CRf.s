%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  64 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ r1_xboole_0(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_68])).

tff(c_36,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    ! [B_29,A_30] :
      ( k1_tarski(B_29) = A_30
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,k1_tarski(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_111,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_8,plain,(
    ! [D_7,B_3] : r2_hidden(D_7,k2_tarski(D_7,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_120,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_120])).

tff(c_128,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_139,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [D_31,B_32,A_33] :
      ( D_31 = B_32
      | D_31 = A_33
      | ~ r2_hidden(D_31,k2_tarski(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [D_31,A_8] :
      ( D_31 = A_8
      | D_31 = A_8
      | ~ r2_hidden(D_31,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_90])).

tff(c_148,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_139,c_96])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  
% 1.86/1.18  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.86/1.18  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.86/1.18  tff(f_45, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.86/1.18  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.86/1.18  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.86/1.18  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.86/1.18  tff(c_34, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.18  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.18  tff(c_68, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~r1_xboole_0(k1_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.86/1.18  tff(c_73, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_68])).
% 1.86/1.18  tff(c_36, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.18  tff(c_75, plain, (![B_29, A_30]: (k1_tarski(B_29)=A_30 | k1_xboole_0=A_30 | ~r1_tarski(A_30, k1_tarski(B_29)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.18  tff(c_85, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_75])).
% 1.86/1.18  tff(c_111, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_85])).
% 1.86/1.18  tff(c_8, plain, (![D_7, B_3]: (r2_hidden(D_7, k2_tarski(D_7, B_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.86/1.18  tff(c_120, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111, c_8])).
% 1.86/1.18  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_120])).
% 1.86/1.18  tff(c_128, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_85])).
% 1.86/1.18  tff(c_139, plain, (r2_hidden('#skF_3', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 1.86/1.18  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.18  tff(c_90, plain, (![D_31, B_32, A_33]: (D_31=B_32 | D_31=A_33 | ~r2_hidden(D_31, k2_tarski(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.86/1.18  tff(c_96, plain, (![D_31, A_8]: (D_31=A_8 | D_31=A_8 | ~r2_hidden(D_31, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_90])).
% 1.86/1.18  tff(c_148, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_139, c_96])).
% 1.86/1.18  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_148])).
% 1.86/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  Inference rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Ref     : 0
% 1.86/1.18  #Sup     : 25
% 1.86/1.18  #Fact    : 0
% 1.86/1.18  #Define  : 0
% 1.86/1.18  #Split   : 1
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 1
% 1.86/1.18  #Demod        : 6
% 1.86/1.18  #Tautology    : 15
% 1.86/1.18  #SimpNegUnit  : 2
% 1.86/1.18  #BackRed      : 3
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.19  Preprocessing        : 0.28
% 1.86/1.19  Parsing              : 0.14
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.13
% 1.86/1.19  Inferencing          : 0.04
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.03
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.43
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
