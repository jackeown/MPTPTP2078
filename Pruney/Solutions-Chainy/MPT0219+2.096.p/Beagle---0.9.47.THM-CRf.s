%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:01 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  44 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_54,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_161,plain,(
    ! [A_57,B_58,C_59,D_60] : k2_xboole_0(k1_enumset1(A_57,B_58,C_59),k1_tarski(D_60)) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,(
    ! [A_21,B_22,D_60] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(D_60)) = k2_enumset1(A_21,A_21,B_22,D_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_161])).

tff(c_174,plain,(
    ! [A_61,B_62,D_63] : k2_xboole_0(k2_tarski(A_61,B_62),k1_tarski(D_63)) = k1_enumset1(A_61,B_62,D_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_170])).

tff(c_183,plain,(
    ! [A_20,D_63] : k2_xboole_0(k1_tarski(A_20),k1_tarski(D_63)) = k1_enumset1(A_20,A_20,D_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_174])).

tff(c_187,plain,(
    ! [A_64,D_65] : k2_xboole_0(k1_tarski(A_64),k1_tarski(D_65)) = k2_tarski(A_64,D_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_183])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_56])).

tff(c_30,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_211,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_30])).

tff(c_113,plain,(
    ! [D_45,B_46,A_47] :
      ( D_45 = B_46
      | D_45 = A_47
      | ~ r2_hidden(D_45,k2_tarski(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [D_45,A_20] :
      ( D_45 = A_20
      | D_45 = A_20
      | ~ r2_hidden(D_45,k1_tarski(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_113])).

tff(c_223,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_211,c_122])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:28:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.00/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.00/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.00/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.00/1.23  
% 2.00/1.24  tff(f_64, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.00/1.24  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.00/1.24  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.00/1.24  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.00/1.24  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.00/1.24  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.00/1.24  tff(c_54, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.24  tff(c_50, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.00/1.24  tff(c_48, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.24  tff(c_52, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.24  tff(c_161, plain, (![A_57, B_58, C_59, D_60]: (k2_xboole_0(k1_enumset1(A_57, B_58, C_59), k1_tarski(D_60))=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.24  tff(c_170, plain, (![A_21, B_22, D_60]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(D_60))=k2_enumset1(A_21, A_21, B_22, D_60))), inference(superposition, [status(thm), theory('equality')], [c_50, c_161])).
% 2.00/1.24  tff(c_174, plain, (![A_61, B_62, D_63]: (k2_xboole_0(k2_tarski(A_61, B_62), k1_tarski(D_63))=k1_enumset1(A_61, B_62, D_63))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_170])).
% 2.00/1.24  tff(c_183, plain, (![A_20, D_63]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(D_63))=k1_enumset1(A_20, A_20, D_63))), inference(superposition, [status(thm), theory('equality')], [c_48, c_174])).
% 2.00/1.24  tff(c_187, plain, (![A_64, D_65]: (k2_xboole_0(k1_tarski(A_64), k1_tarski(D_65))=k2_tarski(A_64, D_65))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_183])).
% 2.00/1.24  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.24  tff(c_193, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_187, c_56])).
% 2.00/1.24  tff(c_30, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.24  tff(c_211, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_30])).
% 2.00/1.24  tff(c_113, plain, (![D_45, B_46, A_47]: (D_45=B_46 | D_45=A_47 | ~r2_hidden(D_45, k2_tarski(A_47, B_46)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.24  tff(c_122, plain, (![D_45, A_20]: (D_45=A_20 | D_45=A_20 | ~r2_hidden(D_45, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_113])).
% 2.00/1.24  tff(c_223, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_211, c_122])).
% 2.00/1.24  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_223])).
% 2.00/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  Inference rules
% 2.00/1.24  ----------------------
% 2.00/1.24  #Ref     : 0
% 2.00/1.24  #Sup     : 40
% 2.00/1.24  #Fact    : 0
% 2.00/1.24  #Define  : 0
% 2.00/1.24  #Split   : 0
% 2.00/1.24  #Chain   : 0
% 2.00/1.24  #Close   : 0
% 2.00/1.24  
% 2.00/1.24  Ordering : KBO
% 2.00/1.24  
% 2.00/1.24  Simplification rules
% 2.00/1.24  ----------------------
% 2.00/1.24  #Subsume      : 1
% 2.00/1.24  #Demod        : 9
% 2.00/1.24  #Tautology    : 30
% 2.00/1.24  #SimpNegUnit  : 1
% 2.00/1.24  #BackRed      : 0
% 2.00/1.24  
% 2.00/1.24  #Partial instantiations: 0
% 2.00/1.24  #Strategies tried      : 1
% 2.00/1.24  
% 2.00/1.24  Timing (in seconds)
% 2.00/1.24  ----------------------
% 2.00/1.25  Preprocessing        : 0.32
% 2.00/1.25  Parsing              : 0.16
% 2.00/1.25  CNF conversion       : 0.02
% 2.00/1.25  Main loop            : 0.15
% 2.00/1.25  Inferencing          : 0.05
% 2.00/1.25  Reduction            : 0.05
% 2.00/1.25  Demodulation         : 0.04
% 2.00/1.25  BG Simplification    : 0.01
% 2.00/1.25  Subsumption          : 0.03
% 2.00/1.25  Abstraction          : 0.01
% 2.00/1.25  MUC search           : 0.00
% 2.00/1.25  Cooper               : 0.00
% 2.00/1.25  Total                : 0.49
% 2.00/1.25  Index Insertion      : 0.00
% 2.00/1.25  Index Deletion       : 0.00
% 2.00/1.25  Index Matching       : 0.00
% 2.00/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
