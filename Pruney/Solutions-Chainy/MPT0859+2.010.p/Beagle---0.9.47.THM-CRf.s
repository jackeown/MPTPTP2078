%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:59 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  55 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   51 (  93 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_44,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_45,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(k2_mcart_1(A_38),C_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_65])).

tff(c_70,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_71,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_42])).

tff(c_87,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k1_mcart_1(A_59),B_60)
      | ~ r2_hidden(A_59,k2_zfmisc_1(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [C_70,F_68,A_72,B_71,D_69] :
      ( F_68 = D_69
      | F_68 = C_70
      | F_68 = B_71
      | F_68 = A_72
      | ~ r2_hidden(F_68,k2_enumset1(A_72,B_71,C_70,D_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [F_91,C_92,B_93,A_94] :
      ( F_91 = C_92
      | F_91 = B_93
      | F_91 = A_94
      | F_91 = A_94
      | ~ r2_hidden(F_91,k1_enumset1(A_94,B_93,C_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_177,plain,(
    ! [F_95,B_96,A_97] :
      ( F_95 = B_96
      | F_95 = A_97
      | F_95 = A_97
      | F_95 = A_97
      | ~ r2_hidden(F_95,k2_tarski(A_97,B_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_186,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_90,c_177])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_70,c_85,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.26  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.26  
% 2.06/1.26  %Foreground sorts:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Background operators:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Foreground operators:
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.06/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.06/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.06/1.26  
% 2.06/1.27  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.06/1.27  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.06/1.27  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.27  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.06/1.27  tff(f_47, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.06/1.27  tff(c_44, plain, (k1_mcart_1('#skF_3')!='#skF_4' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.27  tff(c_45, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_44])).
% 2.06/1.27  tff(c_40, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.27  tff(c_63, plain, (![A_38, C_39, B_40]: (r2_hidden(k2_mcart_1(A_38), C_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.27  tff(c_65, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_40, c_63])).
% 2.06/1.27  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_65])).
% 2.06/1.27  tff(c_70, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.06/1.27  tff(c_71, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 2.06/1.27  tff(c_42, plain, (k1_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.27  tff(c_85, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_42])).
% 2.06/1.27  tff(c_87, plain, (![A_59, B_60, C_61]: (r2_hidden(k1_mcart_1(A_59), B_60) | ~r2_hidden(A_59, k2_zfmisc_1(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.27  tff(c_90, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_87])).
% 2.06/1.27  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.27  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.27  tff(c_117, plain, (![C_70, F_68, A_72, B_71, D_69]: (F_68=D_69 | F_68=C_70 | F_68=B_71 | F_68=A_72 | ~r2_hidden(F_68, k2_enumset1(A_72, B_71, C_70, D_69)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.27  tff(c_158, plain, (![F_91, C_92, B_93, A_94]: (F_91=C_92 | F_91=B_93 | F_91=A_94 | F_91=A_94 | ~r2_hidden(F_91, k1_enumset1(A_94, B_93, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_117])).
% 2.06/1.27  tff(c_177, plain, (![F_95, B_96, A_97]: (F_95=B_96 | F_95=A_97 | F_95=A_97 | F_95=A_97 | ~r2_hidden(F_95, k2_tarski(A_97, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_158])).
% 2.06/1.27  tff(c_186, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_90, c_177])).
% 2.06/1.27  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_70, c_85, c_186])).
% 2.06/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  Inference rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Ref     : 0
% 2.06/1.27  #Sup     : 29
% 2.06/1.27  #Fact    : 0
% 2.06/1.27  #Define  : 0
% 2.06/1.27  #Split   : 1
% 2.06/1.27  #Chain   : 0
% 2.06/1.27  #Close   : 0
% 2.06/1.27  
% 2.06/1.27  Ordering : KBO
% 2.06/1.27  
% 2.06/1.27  Simplification rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Subsume      : 1
% 2.06/1.27  #Demod        : 4
% 2.06/1.27  #Tautology    : 18
% 2.06/1.27  #SimpNegUnit  : 2
% 2.06/1.27  #BackRed      : 0
% 2.06/1.27  
% 2.06/1.27  #Partial instantiations: 0
% 2.06/1.27  #Strategies tried      : 1
% 2.06/1.27  
% 2.06/1.27  Timing (in seconds)
% 2.06/1.27  ----------------------
% 2.06/1.27  Preprocessing        : 0.29
% 2.06/1.27  Parsing              : 0.15
% 2.06/1.27  CNF conversion       : 0.02
% 2.06/1.27  Main loop            : 0.20
% 2.06/1.27  Inferencing          : 0.07
% 2.06/1.27  Reduction            : 0.06
% 2.06/1.27  Demodulation         : 0.04
% 2.06/1.27  BG Simplification    : 0.01
% 2.06/1.27  Subsumption          : 0.04
% 2.06/1.27  Abstraction          : 0.01
% 2.06/1.27  MUC search           : 0.00
% 2.06/1.27  Cooper               : 0.00
% 2.06/1.27  Total                : 0.52
% 2.06/1.27  Index Insertion      : 0.00
% 2.06/1.27  Index Deletion       : 0.00
% 2.06/1.27  Index Matching       : 0.00
% 2.06/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
