%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:02 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    4
%              Number of atoms          :   52 (  94 expanded)
%              Number of equality atoms :   32 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_46,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_hidden(k2_mcart_1(A_50),C_51)
      | ~ r2_hidden(A_50,k2_zfmisc_1(B_52,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_106])).

tff(c_111,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(k2_tarski(A_53,B_54),k1_tarski(B_54)) = k1_tarski(A_53)
      | B_54 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [C_18,B_17] : ~ r2_hidden(C_18,k4_xboole_0(B_17,k1_tarski(C_18))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_130,plain,(
    ! [B_55,A_56] :
      ( ~ r2_hidden(B_55,k1_tarski(A_56))
      | B_55 = A_56 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_36])).

tff(c_133,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_109,c_130])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_133])).

tff(c_142,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_151,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_48])).

tff(c_141,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_191,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(k1_mcart_1(A_78),B_79)
      | ~ r2_hidden(A_78,k2_zfmisc_1(B_79,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_194,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_191])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_246,plain,(
    ! [E_97,C_98,B_99,A_100] :
      ( E_97 = C_98
      | E_97 = B_99
      | E_97 = A_100
      | ~ r2_hidden(E_97,k1_enumset1(A_100,B_99,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_276,plain,(
    ! [E_105,B_106,A_107] :
      ( E_105 = B_106
      | E_105 = A_107
      | E_105 = A_107
      | ~ r2_hidden(E_105,k2_tarski(A_107,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_246])).

tff(c_282,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_194,c_276])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_151,c_141,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.33  
% 2.05/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.05/1.33  
% 2.05/1.33  %Foreground sorts:
% 2.05/1.33  
% 2.05/1.33  
% 2.05/1.33  %Background operators:
% 2.05/1.33  
% 2.05/1.33  
% 2.05/1.33  %Foreground operators:
% 2.05/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.05/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.05/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.05/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.05/1.33  
% 2.05/1.34  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.05/1.34  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.05/1.34  tff(f_51, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.05/1.34  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.05/1.34  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.34  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.05/1.34  tff(c_46, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.05/1.34  tff(c_58, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_46])).
% 2.05/1.34  tff(c_44, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.05/1.34  tff(c_106, plain, (![A_50, C_51, B_52]: (r2_hidden(k2_mcart_1(A_50), C_51) | ~r2_hidden(A_50, k2_zfmisc_1(B_52, C_51)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.05/1.34  tff(c_109, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_106])).
% 2.05/1.34  tff(c_111, plain, (![A_53, B_54]: (k4_xboole_0(k2_tarski(A_53, B_54), k1_tarski(B_54))=k1_tarski(A_53) | B_54=A_53)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.34  tff(c_36, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.34  tff(c_130, plain, (![B_55, A_56]: (~r2_hidden(B_55, k1_tarski(A_56)) | B_55=A_56)), inference(superposition, [status(thm), theory('equality')], [c_111, c_36])).
% 2.05/1.34  tff(c_133, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_109, c_130])).
% 2.05/1.34  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_133])).
% 2.05/1.34  tff(c_142, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.05/1.34  tff(c_48, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.05/1.34  tff(c_151, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_48])).
% 2.05/1.34  tff(c_141, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 2.05/1.34  tff(c_191, plain, (![A_78, B_79, C_80]: (r2_hidden(k1_mcart_1(A_78), B_79) | ~r2_hidden(A_78, k2_zfmisc_1(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.05/1.34  tff(c_194, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_191])).
% 2.05/1.34  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.05/1.34  tff(c_246, plain, (![E_97, C_98, B_99, A_100]: (E_97=C_98 | E_97=B_99 | E_97=A_100 | ~r2_hidden(E_97, k1_enumset1(A_100, B_99, C_98)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.34  tff(c_276, plain, (![E_105, B_106, A_107]: (E_105=B_106 | E_105=A_107 | E_105=A_107 | ~r2_hidden(E_105, k2_tarski(A_107, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_246])).
% 2.05/1.34  tff(c_282, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_194, c_276])).
% 2.05/1.34  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_151, c_141, c_282])).
% 2.05/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.34  
% 2.05/1.34  Inference rules
% 2.05/1.34  ----------------------
% 2.05/1.34  #Ref     : 0
% 2.05/1.34  #Sup     : 54
% 2.05/1.34  #Fact    : 0
% 2.05/1.34  #Define  : 0
% 2.05/1.34  #Split   : 1
% 2.05/1.34  #Chain   : 0
% 2.05/1.34  #Close   : 0
% 2.05/1.34  
% 2.05/1.34  Ordering : KBO
% 2.05/1.34  
% 2.05/1.34  Simplification rules
% 2.05/1.34  ----------------------
% 2.05/1.34  #Subsume      : 2
% 2.05/1.34  #Demod        : 7
% 2.05/1.34  #Tautology    : 30
% 2.05/1.34  #SimpNegUnit  : 2
% 2.05/1.34  #BackRed      : 0
% 2.05/1.34  
% 2.05/1.34  #Partial instantiations: 0
% 2.05/1.34  #Strategies tried      : 1
% 2.05/1.34  
% 2.05/1.34  Timing (in seconds)
% 2.05/1.34  ----------------------
% 2.05/1.35  Preprocessing        : 0.30
% 2.05/1.35  Parsing              : 0.15
% 2.05/1.35  CNF conversion       : 0.02
% 2.05/1.35  Main loop            : 0.22
% 2.05/1.35  Inferencing          : 0.08
% 2.05/1.35  Reduction            : 0.07
% 2.05/1.35  Demodulation         : 0.05
% 2.05/1.35  BG Simplification    : 0.01
% 2.05/1.35  Subsumption          : 0.04
% 2.05/1.35  Abstraction          : 0.01
% 2.05/1.35  MUC search           : 0.00
% 2.05/1.35  Cooper               : 0.00
% 2.05/1.35  Total                : 0.54
% 2.05/1.35  Index Insertion      : 0.00
% 2.05/1.35  Index Deletion       : 0.00
% 2.05/1.35  Index Matching       : 0.00
% 2.05/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
