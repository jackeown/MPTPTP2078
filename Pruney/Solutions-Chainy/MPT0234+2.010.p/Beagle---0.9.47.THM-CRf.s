%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:42 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   39 (  69 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  96 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [B_17,C_18] :
      ( k4_xboole_0(k2_tarski(B_17,B_17),C_18) = k1_tarski(B_17)
      | r2_hidden(B_17,C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_35,plain,(
    ! [B_17,C_18] :
      ( k4_xboole_0(k1_tarski(B_17),C_18) = k1_tarski(B_17)
      | r2_hidden(B_17,C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_97,plain,(
    ! [A_37,B_38] : k2_xboole_0(k4_xboole_0(A_37,B_38),k4_xboole_0(B_38,A_37)) = k5_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [B_57,C_58] :
      ( k2_xboole_0(k1_tarski(B_57),k4_xboole_0(C_58,k1_tarski(B_57))) = k5_xboole_0(k1_tarski(B_57),C_58)
      | r2_hidden(B_57,C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_97])).

tff(c_213,plain,(
    ! [B_57,B_17] :
      ( k5_xboole_0(k1_tarski(B_57),k1_tarski(B_17)) = k2_xboole_0(k1_tarski(B_57),k1_tarski(B_17))
      | r2_hidden(B_57,k1_tarski(B_17))
      | r2_hidden(B_17,k1_tarski(B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_199])).

tff(c_219,plain,(
    ! [B_61,B_62] :
      ( k5_xboole_0(k1_tarski(B_61),k1_tarski(B_62)) = k2_tarski(B_61,B_62)
      | r2_hidden(B_61,k1_tarski(B_62))
      | r2_hidden(B_62,k1_tarski(B_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_213])).

tff(c_32,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_230,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_4'))
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_32])).

tff(c_232,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_235,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_235])).

tff(c_240,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_267,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_240,c_4])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.23  
% 1.98/1.24  tff(f_57, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.98/1.24  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.98/1.24  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.98/1.24  tff(f_51, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.98/1.24  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.98/1.24  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.98/1.24  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.24  tff(c_16, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.24  tff(c_18, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.24  tff(c_28, plain, (![B_17, C_18]: (k4_xboole_0(k2_tarski(B_17, B_17), C_18)=k1_tarski(B_17) | r2_hidden(B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.24  tff(c_35, plain, (![B_17, C_18]: (k4_xboole_0(k1_tarski(B_17), C_18)=k1_tarski(B_17) | r2_hidden(B_17, C_18))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 1.98/1.24  tff(c_97, plain, (![A_37, B_38]: (k2_xboole_0(k4_xboole_0(A_37, B_38), k4_xboole_0(B_38, A_37))=k5_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.24  tff(c_199, plain, (![B_57, C_58]: (k2_xboole_0(k1_tarski(B_57), k4_xboole_0(C_58, k1_tarski(B_57)))=k5_xboole_0(k1_tarski(B_57), C_58) | r2_hidden(B_57, C_58))), inference(superposition, [status(thm), theory('equality')], [c_35, c_97])).
% 1.98/1.24  tff(c_213, plain, (![B_57, B_17]: (k5_xboole_0(k1_tarski(B_57), k1_tarski(B_17))=k2_xboole_0(k1_tarski(B_57), k1_tarski(B_17)) | r2_hidden(B_57, k1_tarski(B_17)) | r2_hidden(B_17, k1_tarski(B_57)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_199])).
% 1.98/1.24  tff(c_219, plain, (![B_61, B_62]: (k5_xboole_0(k1_tarski(B_61), k1_tarski(B_62))=k2_tarski(B_61, B_62) | r2_hidden(B_61, k1_tarski(B_62)) | r2_hidden(B_62, k1_tarski(B_61)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_213])).
% 1.98/1.24  tff(c_32, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.24  tff(c_230, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4')) | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_219, c_32])).
% 1.98/1.24  tff(c_232, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_230])).
% 1.98/1.24  tff(c_4, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.24  tff(c_235, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_232, c_4])).
% 1.98/1.24  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_235])).
% 1.98/1.24  tff(c_240, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_230])).
% 1.98/1.24  tff(c_267, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_240, c_4])).
% 1.98/1.24  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_267])).
% 1.98/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  Inference rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Ref     : 0
% 1.98/1.24  #Sup     : 50
% 1.98/1.24  #Fact    : 0
% 1.98/1.24  #Define  : 0
% 1.98/1.24  #Split   : 1
% 1.98/1.24  #Chain   : 0
% 1.98/1.24  #Close   : 0
% 1.98/1.24  
% 1.98/1.24  Ordering : KBO
% 1.98/1.24  
% 1.98/1.24  Simplification rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Subsume      : 2
% 1.98/1.24  #Demod        : 10
% 1.98/1.24  #Tautology    : 32
% 1.98/1.24  #SimpNegUnit  : 2
% 1.98/1.24  #BackRed      : 0
% 1.98/1.24  
% 1.98/1.24  #Partial instantiations: 0
% 1.98/1.24  #Strategies tried      : 1
% 1.98/1.24  
% 1.98/1.24  Timing (in seconds)
% 1.98/1.24  ----------------------
% 1.98/1.25  Preprocessing        : 0.30
% 1.98/1.25  Parsing              : 0.16
% 1.98/1.25  CNF conversion       : 0.02
% 1.98/1.25  Main loop            : 0.19
% 1.98/1.25  Inferencing          : 0.07
% 1.98/1.25  Reduction            : 0.05
% 1.98/1.25  Demodulation         : 0.04
% 1.98/1.25  BG Simplification    : 0.01
% 1.98/1.25  Subsumption          : 0.04
% 1.98/1.25  Abstraction          : 0.01
% 1.98/1.25  MUC search           : 0.00
% 1.98/1.25  Cooper               : 0.00
% 1.98/1.25  Total                : 0.51
% 1.98/1.25  Index Insertion      : 0.00
% 1.98/1.25  Index Deletion       : 0.00
% 1.98/1.25  Index Matching       : 0.00
% 1.98/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
