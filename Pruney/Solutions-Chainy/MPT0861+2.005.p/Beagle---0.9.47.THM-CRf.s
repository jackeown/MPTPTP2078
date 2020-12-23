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
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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

tff(c_44,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    ! [A_37,C_38,B_39] :
      ( k2_mcart_1(A_37) = C_38
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_39,k1_tarski(C_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_90])).

tff(c_95,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_96,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_103,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42])).

tff(c_155,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(k1_mcart_1(A_65),B_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_155])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_159,plain,(
    ! [E_68,C_69,B_70,A_71] :
      ( E_68 = C_69
      | E_68 = B_70
      | E_68 = A_71
      | ~ r2_hidden(E_68,k1_enumset1(A_71,B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_178,plain,(
    ! [E_72,B_73,A_74] :
      ( E_72 = B_73
      | E_72 = A_74
      | E_72 = A_74
      | ~ r2_hidden(E_72,k2_tarski(A_74,B_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_159])).

tff(c_181,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_158,c_178])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_95,c_103,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.09/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.09/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.09/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.09/1.32  
% 2.09/1.33  tff(f_67, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.09/1.33  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.09/1.33  tff(f_52, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.09/1.33  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.33  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.33  tff(c_44, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.33  tff(c_54, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_44])).
% 2.09/1.33  tff(c_40, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.33  tff(c_87, plain, (![A_37, C_38, B_39]: (k2_mcart_1(A_37)=C_38 | ~r2_hidden(A_37, k2_zfmisc_1(B_39, k1_tarski(C_38))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.33  tff(c_90, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_40, c_87])).
% 2.09/1.33  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_90])).
% 2.09/1.33  tff(c_95, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.09/1.33  tff(c_96, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.09/1.33  tff(c_42, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.33  tff(c_103, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42])).
% 2.09/1.33  tff(c_155, plain, (![A_65, B_66, C_67]: (r2_hidden(k1_mcart_1(A_65), B_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.33  tff(c_158, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_155])).
% 2.09/1.33  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.33  tff(c_159, plain, (![E_68, C_69, B_70, A_71]: (E_68=C_69 | E_68=B_70 | E_68=A_71 | ~r2_hidden(E_68, k1_enumset1(A_71, B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.33  tff(c_178, plain, (![E_72, B_73, A_74]: (E_72=B_73 | E_72=A_74 | E_72=A_74 | ~r2_hidden(E_72, k2_tarski(A_74, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_159])).
% 2.09/1.33  tff(c_181, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_158, c_178])).
% 2.09/1.33  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_95, c_103, c_181])).
% 2.09/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  Inference rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Ref     : 0
% 2.09/1.33  #Sup     : 32
% 2.09/1.33  #Fact    : 0
% 2.09/1.33  #Define  : 0
% 2.09/1.33  #Split   : 1
% 2.09/1.33  #Chain   : 0
% 2.09/1.33  #Close   : 0
% 2.09/1.33  
% 2.09/1.33  Ordering : KBO
% 2.09/1.33  
% 2.09/1.33  Simplification rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Subsume      : 2
% 2.09/1.33  #Demod        : 8
% 2.09/1.33  #Tautology    : 19
% 2.09/1.33  #SimpNegUnit  : 2
% 2.09/1.33  #BackRed      : 0
% 2.09/1.33  
% 2.09/1.33  #Partial instantiations: 0
% 2.09/1.33  #Strategies tried      : 1
% 2.09/1.33  
% 2.09/1.33  Timing (in seconds)
% 2.09/1.33  ----------------------
% 2.09/1.33  Preprocessing        : 0.29
% 2.09/1.33  Parsing              : 0.15
% 2.09/1.33  CNF conversion       : 0.02
% 2.09/1.33  Main loop            : 0.21
% 2.09/1.33  Inferencing          : 0.08
% 2.09/1.33  Reduction            : 0.06
% 2.09/1.33  Demodulation         : 0.05
% 2.09/1.33  BG Simplification    : 0.01
% 2.09/1.33  Subsumption          : 0.03
% 2.09/1.33  Abstraction          : 0.01
% 2.09/1.33  MUC search           : 0.00
% 2.09/1.33  Cooper               : 0.00
% 2.09/1.33  Total                : 0.53
% 2.09/1.33  Index Insertion      : 0.00
% 2.09/1.33  Index Deletion       : 0.00
% 2.09/1.33  Index Matching       : 0.00
% 2.09/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
