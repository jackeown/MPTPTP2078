%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  56 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(B_38,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_38,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    ! [B_38,A_37] : k2_xboole_0(B_38,A_37) = k2_xboole_0(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_38])).

tff(c_42,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_157,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_42])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_213,plain,
    ( k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_157,c_8])).

tff(c_216,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_213])).

tff(c_20,plain,(
    ! [D_17,A_12] : r2_hidden(D_17,k2_tarski(A_12,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_264,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    ! [D_53,B_54,A_55] :
      ( r2_hidden(D_53,B_54)
      | ~ r1_tarski(k2_tarski(A_55,D_53),B_54) ) ),
    inference(resolution,[status(thm)],[c_20,c_264])).

tff(c_314,plain,(
    ! [D_60,A_61,B_62] : r2_hidden(D_60,k2_xboole_0(k2_tarski(A_61,D_60),B_62)) ),
    inference(resolution,[status(thm)],[c_14,c_274])).

tff(c_333,plain,(
    ! [D_63,A_64,A_65] : r2_hidden(D_63,k2_xboole_0(A_64,k2_tarski(A_65,D_63))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_314])).

tff(c_381,plain,(
    ! [B_72,A_73,A_74] : r2_hidden(B_72,k2_xboole_0(A_73,k2_tarski(B_72,A_74))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_333])).

tff(c_386,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_381])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.28  
% 2.06/1.29  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.06/1.29  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/1.29  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.06/1.29  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.06/1.29  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.29  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.29  tff(c_40, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.29  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.29  tff(c_16, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.29  tff(c_97, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.29  tff(c_134, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(B_38, A_37))), inference(superposition, [status(thm), theory('equality')], [c_16, c_97])).
% 2.06/1.29  tff(c_38, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.29  tff(c_140, plain, (![B_38, A_37]: (k2_xboole_0(B_38, A_37)=k2_xboole_0(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_134, c_38])).
% 2.06/1.29  tff(c_42, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.29  tff(c_157, plain, (r1_tarski(k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_42])).
% 2.06/1.29  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.29  tff(c_213, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_157, c_8])).
% 2.06/1.29  tff(c_216, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_213])).
% 2.06/1.29  tff(c_20, plain, (![D_17, A_12]: (r2_hidden(D_17, k2_tarski(A_12, D_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.29  tff(c_264, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.29  tff(c_274, plain, (![D_53, B_54, A_55]: (r2_hidden(D_53, B_54) | ~r1_tarski(k2_tarski(A_55, D_53), B_54))), inference(resolution, [status(thm)], [c_20, c_264])).
% 2.06/1.29  tff(c_314, plain, (![D_60, A_61, B_62]: (r2_hidden(D_60, k2_xboole_0(k2_tarski(A_61, D_60), B_62)))), inference(resolution, [status(thm)], [c_14, c_274])).
% 2.06/1.29  tff(c_333, plain, (![D_63, A_64, A_65]: (r2_hidden(D_63, k2_xboole_0(A_64, k2_tarski(A_65, D_63))))), inference(superposition, [status(thm), theory('equality')], [c_140, c_314])).
% 2.06/1.29  tff(c_381, plain, (![B_72, A_73, A_74]: (r2_hidden(B_72, k2_xboole_0(A_73, k2_tarski(B_72, A_74))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_333])).
% 2.06/1.29  tff(c_386, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_216, c_381])).
% 2.06/1.29  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_386])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 86
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 1
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 1
% 2.06/1.29  #Demod        : 31
% 2.06/1.29  #Tautology    : 51
% 2.06/1.29  #SimpNegUnit  : 1
% 2.06/1.29  #BackRed      : 2
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.30
% 2.06/1.29  Parsing              : 0.16
% 2.06/1.30  CNF conversion       : 0.02
% 2.06/1.30  Main loop            : 0.24
% 2.06/1.30  Inferencing          : 0.08
% 2.06/1.30  Reduction            : 0.09
% 2.06/1.30  Demodulation         : 0.07
% 2.06/1.30  BG Simplification    : 0.01
% 2.06/1.30  Subsumption          : 0.05
% 2.06/1.30  Abstraction          : 0.01
% 2.06/1.30  MUC search           : 0.00
% 2.06/1.30  Cooper               : 0.00
% 2.06/1.30  Total                : 0.57
% 2.06/1.30  Index Insertion      : 0.00
% 2.06/1.30  Index Deletion       : 0.00
% 2.06/1.30  Index Matching       : 0.00
% 2.06/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
