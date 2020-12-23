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
% DateTime   : Thu Dec  3 09:48:56 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   39 (  57 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  73 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    ! [B_41,A_42] :
      ( k1_tarski(B_41) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_103])).

tff(c_118,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_24,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_148,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_24])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [D_30,A_7] :
      ( ~ r2_hidden(D_30,k1_xboole_0)
      | ~ r2_hidden(D_30,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_159,plain,(
    ! [A_7] : ~ r2_hidden('#skF_5',A_7) ),
    inference(resolution,[status(thm)],[c_148,c_88])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_148])).

tff(c_163,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_183,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_24])).

tff(c_22,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_183,c_22])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.97/1.23  
% 1.97/1.23  %Foreground sorts:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Background operators:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Foreground operators:
% 1.97/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.97/1.23  
% 1.97/1.24  tff(f_61, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.97/1.24  tff(f_56, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.97/1.24  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.97/1.24  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.97/1.24  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.97/1.24  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.24  tff(c_48, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.24  tff(c_103, plain, (![B_41, A_42]: (k1_tarski(B_41)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_41)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.24  tff(c_115, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_103])).
% 1.97/1.24  tff(c_118, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_115])).
% 1.97/1.24  tff(c_24, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.24  tff(c_148, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_24])).
% 1.97/1.24  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.24  tff(c_85, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.24  tff(c_88, plain, (![D_30, A_7]: (~r2_hidden(D_30, k1_xboole_0) | ~r2_hidden(D_30, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_85])).
% 1.97/1.24  tff(c_159, plain, (![A_7]: (~r2_hidden('#skF_5', A_7))), inference(resolution, [status(thm)], [c_148, c_88])).
% 1.97/1.24  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_148])).
% 1.97/1.24  tff(c_163, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_115])).
% 1.97/1.24  tff(c_183, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_24])).
% 1.97/1.24  tff(c_22, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.24  tff(c_195, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_183, c_22])).
% 1.97/1.24  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_195])).
% 1.97/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  Inference rules
% 1.97/1.24  ----------------------
% 1.97/1.24  #Ref     : 0
% 1.97/1.24  #Sup     : 35
% 1.97/1.24  #Fact    : 0
% 1.97/1.24  #Define  : 0
% 1.97/1.24  #Split   : 1
% 1.97/1.24  #Chain   : 0
% 1.97/1.24  #Close   : 0
% 1.97/1.24  
% 1.97/1.24  Ordering : KBO
% 1.97/1.24  
% 1.97/1.24  Simplification rules
% 1.97/1.24  ----------------------
% 1.97/1.24  #Subsume      : 1
% 1.97/1.24  #Demod        : 15
% 1.97/1.24  #Tautology    : 26
% 1.97/1.24  #SimpNegUnit  : 2
% 1.97/1.24  #BackRed      : 4
% 1.97/1.24  
% 1.97/1.24  #Partial instantiations: 0
% 1.97/1.24  #Strategies tried      : 1
% 1.97/1.24  
% 1.97/1.24  Timing (in seconds)
% 1.97/1.24  ----------------------
% 1.97/1.24  Preprocessing        : 0.30
% 1.97/1.24  Parsing              : 0.15
% 1.97/1.24  CNF conversion       : 0.02
% 1.97/1.24  Main loop            : 0.15
% 1.97/1.24  Inferencing          : 0.05
% 1.97/1.24  Reduction            : 0.05
% 1.97/1.24  Demodulation         : 0.04
% 1.97/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.03
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.47
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
