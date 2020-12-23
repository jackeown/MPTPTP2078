%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  80 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_127,plain,(
    ! [A_59,C_60,B_61,D_62] :
      ( k1_mcart_1(A_59) = C_60
      | k1_mcart_1(A_59) = B_61
      | ~ r2_hidden(A_59,k2_zfmisc_1(k2_tarski(B_61,C_60),D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,(
    ! [A_68,A_69,D_70] :
      ( k1_mcart_1(A_68) = A_69
      | k1_mcart_1(A_68) = A_69
      | ~ r2_hidden(A_68,k2_zfmisc_1(k1_tarski(A_69),D_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_143,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_140])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_143])).

tff(c_148,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_149,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_155,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_38])).

tff(c_194,plain,(
    ! [A_81,D_82,B_83,C_84] :
      ( r2_hidden(k2_mcart_1(A_81),D_82)
      | ~ r2_hidden(A_81,k2_zfmisc_1(k2_tarski(B_83,C_84),D_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_197,plain,(
    ! [A_85,D_86,A_87] :
      ( r2_hidden(k2_mcart_1(A_85),D_86)
      | ~ r2_hidden(A_85,k2_zfmisc_1(k1_tarski(A_87),D_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_194])).

tff(c_201,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_204,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_201,c_2])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_155,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:06:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.28  
% 2.01/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.01/1.29  
% 2.01/1.29  %Foreground sorts:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Background operators:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Foreground operators:
% 2.01/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.01/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.01/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.29  
% 2.01/1.29  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.01/1.29  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.29  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.01/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.01/1.29  tff(c_40, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.29  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 2.01/1.29  tff(c_36, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.29  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.01/1.29  tff(c_127, plain, (![A_59, C_60, B_61, D_62]: (k1_mcart_1(A_59)=C_60 | k1_mcart_1(A_59)=B_61 | ~r2_hidden(A_59, k2_zfmisc_1(k2_tarski(B_61, C_60), D_62)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.29  tff(c_140, plain, (![A_68, A_69, D_70]: (k1_mcart_1(A_68)=A_69 | k1_mcart_1(A_68)=A_69 | ~r2_hidden(A_68, k2_zfmisc_1(k1_tarski(A_69), D_70)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 2.01/1.29  tff(c_143, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_140])).
% 2.01/1.29  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_143])).
% 2.01/1.29  tff(c_148, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 2.01/1.29  tff(c_149, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.01/1.29  tff(c_38, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.29  tff(c_155, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_38])).
% 2.01/1.29  tff(c_194, plain, (![A_81, D_82, B_83, C_84]: (r2_hidden(k2_mcart_1(A_81), D_82) | ~r2_hidden(A_81, k2_zfmisc_1(k2_tarski(B_83, C_84), D_82)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.29  tff(c_197, plain, (![A_85, D_86, A_87]: (r2_hidden(k2_mcart_1(A_85), D_86) | ~r2_hidden(A_85, k2_zfmisc_1(k1_tarski(A_87), D_86)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_194])).
% 2.01/1.29  tff(c_201, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_197])).
% 2.01/1.29  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.01/1.29  tff(c_204, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_201, c_2])).
% 2.01/1.29  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_155, c_204])).
% 2.01/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  Inference rules
% 2.01/1.29  ----------------------
% 2.01/1.29  #Ref     : 0
% 2.01/1.29  #Sup     : 36
% 2.01/1.29  #Fact    : 0
% 2.01/1.29  #Define  : 0
% 2.01/1.29  #Split   : 2
% 2.01/1.29  #Chain   : 0
% 2.01/1.29  #Close   : 0
% 2.01/1.29  
% 2.01/1.29  Ordering : KBO
% 2.01/1.29  
% 2.01/1.29  Simplification rules
% 2.01/1.29  ----------------------
% 2.01/1.29  #Subsume      : 1
% 2.01/1.30  #Demod        : 4
% 2.01/1.30  #Tautology    : 26
% 2.01/1.30  #SimpNegUnit  : 2
% 2.01/1.30  #BackRed      : 1
% 2.01/1.30  
% 2.01/1.30  #Partial instantiations: 0
% 2.01/1.30  #Strategies tried      : 1
% 2.01/1.30  
% 2.01/1.30  Timing (in seconds)
% 2.01/1.30  ----------------------
% 2.01/1.30  Preprocessing        : 0.33
% 2.01/1.30  Parsing              : 0.18
% 2.01/1.30  CNF conversion       : 0.02
% 2.01/1.30  Main loop            : 0.15
% 2.01/1.30  Inferencing          : 0.05
% 2.01/1.30  Reduction            : 0.05
% 2.01/1.30  Demodulation         : 0.04
% 2.01/1.30  BG Simplification    : 0.01
% 2.01/1.30  Subsumption          : 0.03
% 2.01/1.30  Abstraction          : 0.01
% 2.01/1.30  MUC search           : 0.00
% 2.01/1.30  Cooper               : 0.00
% 2.01/1.30  Total                : 0.50
% 2.01/1.30  Index Insertion      : 0.00
% 2.01/1.30  Index Deletion       : 0.00
% 2.01/1.30  Index Matching       : 0.00
% 2.01/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
