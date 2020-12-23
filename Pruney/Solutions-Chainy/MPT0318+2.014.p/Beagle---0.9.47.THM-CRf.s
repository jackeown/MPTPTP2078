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
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  66 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_26,B_27] : k4_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,(
    ! [A_6] : k4_xboole_0(k1_tarski(A_6),k1_tarski(A_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_122,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | k4_xboole_0(A_32,k1_tarski(B_31)) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_128,plain,(
    ! [A_6] :
      ( ~ r2_hidden(A_6,k1_tarski(A_6))
      | k1_tarski(A_6) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_122])).

tff(c_131,plain,(
    ! [A_6] : k1_tarski(A_6) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_32,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_133,plain,(
    ! [B_34,A_35] :
      ( k1_xboole_0 = B_34
      | k1_xboole_0 = A_35
      | k2_zfmisc_1(A_35,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_133])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_34,c_136])).

tff(c_147,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_153,plain,(
    ! [B_36,A_37] :
      ( k1_xboole_0 = B_36
      | k1_xboole_0 = A_37
      | k2_zfmisc_1(A_37,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_156,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_153])).

tff(c_165,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_156])).

tff(c_148,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_170,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_148])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.20  
% 1.81/1.20  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.81/1.20  tff(f_61, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.81/1.20  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.81/1.20  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.81/1.20  tff(f_46, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.81/1.20  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.81/1.20  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.20  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.81/1.20  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.20  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.81/1.20  tff(c_82, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.20  tff(c_89, plain, (![A_6]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(A_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_82])).
% 1.81/1.20  tff(c_122, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | k4_xboole_0(A_32, k1_tarski(B_31))!=A_32)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.81/1.20  tff(c_128, plain, (![A_6]: (~r2_hidden(A_6, k1_tarski(A_6)) | k1_tarski(A_6)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89, c_122])).
% 1.81/1.20  tff(c_131, plain, (![A_6]: (k1_tarski(A_6)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_128])).
% 1.81/1.20  tff(c_32, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.81/1.20  tff(c_99, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 1.81/1.20  tff(c_133, plain, (![B_34, A_35]: (k1_xboole_0=B_34 | k1_xboole_0=A_35 | k2_zfmisc_1(A_35, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.20  tff(c_136, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_133])).
% 1.81/1.20  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_34, c_136])).
% 1.81/1.20  tff(c_147, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.81/1.20  tff(c_153, plain, (![B_36, A_37]: (k1_xboole_0=B_36 | k1_xboole_0=A_37 | k2_zfmisc_1(A_37, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.20  tff(c_156, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_147, c_153])).
% 1.81/1.20  tff(c_165, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_156])).
% 1.81/1.20  tff(c_148, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.81/1.20  tff(c_170, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_165, c_148])).
% 1.81/1.20  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_170])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 32
% 1.81/1.20  #Fact    : 0
% 1.81/1.20  #Define  : 0
% 1.81/1.20  #Split   : 1
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.21  
% 1.81/1.21  Ordering : KBO
% 1.81/1.21  
% 1.81/1.21  Simplification rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Subsume      : 0
% 1.81/1.21  #Demod        : 6
% 1.81/1.21  #Tautology    : 26
% 1.81/1.21  #SimpNegUnit  : 2
% 1.81/1.21  #BackRed      : 2
% 1.81/1.21  
% 1.81/1.21  #Partial instantiations: 0
% 1.81/1.21  #Strategies tried      : 1
% 1.81/1.21  
% 1.81/1.21  Timing (in seconds)
% 1.81/1.21  ----------------------
% 1.81/1.21  Preprocessing        : 0.31
% 1.81/1.21  Parsing              : 0.15
% 1.81/1.21  CNF conversion       : 0.03
% 1.81/1.21  Main loop            : 0.13
% 1.81/1.21  Inferencing          : 0.04
% 1.81/1.21  Reduction            : 0.04
% 1.81/1.21  Demodulation         : 0.03
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.03
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.46
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
