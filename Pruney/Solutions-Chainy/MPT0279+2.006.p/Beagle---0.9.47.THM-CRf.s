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
% DateTime   : Thu Dec  3 09:53:23 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  43 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_26,plain,(
    ! [C_18,A_14] :
      ( r2_hidden(C_18,k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_39,B_40] :
      ( '#skF_1'(k1_tarski(A_39),B_40) = A_39
      | r1_tarski(k1_tarski(A_39),B_40) ) ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_116,plain,(
    '#skF_1'(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_108,c_36])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,
    ( ~ r2_hidden('#skF_6',k1_zfmisc_1('#skF_6'))
    | r1_tarski(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_4])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_120])).

tff(c_132,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.16  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.69/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.69/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.69/1.16  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.69/1.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.69/1.16  
% 1.69/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.69/1.17  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.69/1.17  tff(f_53, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.69/1.17  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.69/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.17  tff(c_79, plain, (![A_31, B_32]: (~r2_hidden('#skF_1'(A_31, B_32), B_32) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.17  tff(c_88, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_79])).
% 1.69/1.17  tff(c_26, plain, (![C_18, A_14]: (r2_hidden(C_18, k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.69/1.17  tff(c_36, plain, (~r1_tarski(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.69/1.17  tff(c_68, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.17  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.17  tff(c_108, plain, (![A_39, B_40]: ('#skF_1'(k1_tarski(A_39), B_40)=A_39 | r1_tarski(k1_tarski(A_39), B_40))), inference(resolution, [status(thm)], [c_68, c_8])).
% 1.69/1.17  tff(c_116, plain, ('#skF_1'(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_108, c_36])).
% 1.69/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.17  tff(c_120, plain, (~r2_hidden('#skF_6', k1_zfmisc_1('#skF_6')) | r1_tarski(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_4])).
% 1.69/1.17  tff(c_126, plain, (~r2_hidden('#skF_6', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_36, c_120])).
% 1.69/1.17  tff(c_132, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_126])).
% 1.69/1.17  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_132])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 21
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 0
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.17  Ordering : KBO
% 1.69/1.17  
% 1.69/1.17  Simplification rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Subsume      : 0
% 1.69/1.17  #Demod        : 3
% 1.69/1.17  #Tautology    : 10
% 1.69/1.17  #SimpNegUnit  : 2
% 1.69/1.17  #BackRed      : 0
% 1.69/1.17  
% 1.69/1.17  #Partial instantiations: 0
% 1.69/1.17  #Strategies tried      : 1
% 1.69/1.17  
% 1.69/1.17  Timing (in seconds)
% 1.69/1.17  ----------------------
% 1.92/1.18  Preprocessing        : 0.29
% 1.92/1.18  Parsing              : 0.15
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.11
% 1.92/1.18  Inferencing          : 0.04
% 1.92/1.18  Reduction            : 0.03
% 1.92/1.18  Demodulation         : 0.02
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.02
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.43
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.18  Index Matching       : 0.00
% 1.92/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
