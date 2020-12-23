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
% DateTime   : Thu Dec  3 09:54:05 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 (  78 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    ! [D_19,B_20] : r2_hidden(D_19,k2_tarski(D_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_162,plain,(
    ! [A_36,B_37] : k4_xboole_0(k1_tarski(A_36),k2_tarski(A_36,B_37)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_169,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_197,plain,(
    ! [B_41,A_42] :
      ( ~ r2_hidden(B_41,A_42)
      | k4_xboole_0(A_42,k1_tarski(B_41)) != A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_203,plain,(
    ! [A_7] :
      ( ~ r2_hidden(A_7,k1_tarski(A_7))
      | k1_tarski(A_7) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_197])).

tff(c_206,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_203])).

tff(c_94,plain,(
    ! [A_26,B_27] : k4_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_111,plain,(
    ! [B_29,A_30] :
      ( ~ r2_hidden(B_29,A_30)
      | k4_xboole_0(A_30,k1_tarski(B_29)) != A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    ! [A_7] :
      ( ~ r2_hidden(A_7,k1_tarski(A_7))
      | k1_tarski(A_7) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_111])).

tff(c_116,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_114])).

tff(c_36,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_142,plain,(
    ! [B_34,A_35] :
      ( k1_xboole_0 = B_34
      | k1_xboole_0 = A_35
      | k2_zfmisc_1(A_35,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_142])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_38,c_145])).

tff(c_156,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_208,plain,(
    ! [B_44,A_45] :
      ( k1_xboole_0 = B_44
      | k1_xboole_0 = A_45
      | k2_zfmisc_1(A_45,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_211,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_208])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_206,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  
% 1.95/1.20  tff(f_61, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.95/1.20  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.20  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.95/1.20  tff(f_46, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.95/1.20  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.95/1.20  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.95/1.20  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.20  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.95/1.20  tff(c_70, plain, (![D_19, B_20]: (r2_hidden(D_19, k2_tarski(D_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.20  tff(c_73, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_70])).
% 1.95/1.20  tff(c_162, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), k2_tarski(A_36, B_37))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.20  tff(c_169, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_162])).
% 1.95/1.20  tff(c_197, plain, (![B_41, A_42]: (~r2_hidden(B_41, A_42) | k4_xboole_0(A_42, k1_tarski(B_41))!=A_42)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.20  tff(c_203, plain, (![A_7]: (~r2_hidden(A_7, k1_tarski(A_7)) | k1_tarski(A_7)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_197])).
% 1.95/1.20  tff(c_206, plain, (![A_7]: (k1_tarski(A_7)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_203])).
% 1.95/1.20  tff(c_94, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.20  tff(c_101, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 1.95/1.20  tff(c_111, plain, (![B_29, A_30]: (~r2_hidden(B_29, A_30) | k4_xboole_0(A_30, k1_tarski(B_29))!=A_30)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.20  tff(c_114, plain, (![A_7]: (~r2_hidden(A_7, k1_tarski(A_7)) | k1_tarski(A_7)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_111])).
% 1.95/1.20  tff(c_116, plain, (![A_7]: (k1_tarski(A_7)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_114])).
% 1.95/1.20  tff(c_36, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.20  tff(c_89, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 1.95/1.20  tff(c_142, plain, (![B_34, A_35]: (k1_xboole_0=B_34 | k1_xboole_0=A_35 | k2_zfmisc_1(A_35, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.20  tff(c_145, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89, c_142])).
% 1.95/1.20  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_38, c_145])).
% 1.95/1.20  tff(c_156, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 1.95/1.20  tff(c_208, plain, (![B_44, A_45]: (k1_xboole_0=B_44 | k1_xboole_0=A_45 | k2_zfmisc_1(A_45, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.20  tff(c_211, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_156, c_208])).
% 1.95/1.20  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_206, c_211])).
% 1.95/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  Inference rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Ref     : 0
% 1.95/1.20  #Sup     : 44
% 1.95/1.20  #Fact    : 0
% 1.95/1.20  #Define  : 0
% 1.95/1.20  #Split   : 1
% 1.95/1.20  #Chain   : 0
% 1.95/1.20  #Close   : 0
% 1.95/1.20  
% 1.95/1.20  Ordering : KBO
% 1.95/1.20  
% 1.95/1.20  Simplification rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Subsume      : 0
% 1.95/1.20  #Demod        : 7
% 1.95/1.20  #Tautology    : 33
% 1.95/1.20  #SimpNegUnit  : 4
% 1.95/1.20  #BackRed      : 0
% 1.95/1.20  
% 1.95/1.20  #Partial instantiations: 0
% 1.95/1.20  #Strategies tried      : 1
% 1.95/1.20  
% 1.95/1.20  Timing (in seconds)
% 1.95/1.20  ----------------------
% 1.95/1.20  Preprocessing        : 0.30
% 1.95/1.20  Parsing              : 0.15
% 1.95/1.20  CNF conversion       : 0.02
% 1.95/1.20  Main loop            : 0.14
% 1.95/1.20  Inferencing          : 0.05
% 1.95/1.20  Reduction            : 0.05
% 1.95/1.20  Demodulation         : 0.03
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.03
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.46
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
