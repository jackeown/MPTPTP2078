%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  93 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_44,plain,
    ( k2_mcart_1('#skF_7') != '#skF_9'
    | ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(k1_mcart_1(A_65),B_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_100])).

tff(c_105,plain,(
    k2_mcart_1('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_125,plain,(
    ! [A_73,C_74,B_75] :
      ( r2_hidden(k2_mcart_1(A_73),C_74)
      | ~ r2_hidden(A_73,k2_zfmisc_1(B_75,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_40,plain,(
    ! [A_47,B_48] : k1_mcart_1(k4_tarski(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_135,plain,(
    ! [E_82,F_83,A_84,B_85] :
      ( r2_hidden(k4_tarski(E_82,F_83),k2_zfmisc_1(A_84,B_85))
      | ~ r2_hidden(F_83,B_85)
      | ~ r2_hidden(E_82,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_mcart_1(A_44) = B_45
      | ~ r2_hidden(A_44,k2_zfmisc_1(k1_tarski(B_45),C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,(
    ! [E_82,F_83,B_45,B_85] :
      ( k1_mcart_1(k4_tarski(E_82,F_83)) = B_45
      | ~ r2_hidden(F_83,B_85)
      | ~ r2_hidden(E_82,k1_tarski(B_45)) ) ),
    inference(resolution,[status(thm)],[c_135,c_38])).

tff(c_145,plain,(
    ! [E_82,B_45,F_83,B_85] :
      ( E_82 = B_45
      | ~ r2_hidden(F_83,B_85)
      | ~ r2_hidden(E_82,k1_tarski(B_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_139])).

tff(c_150,plain,(
    ! [F_83,B_85] : ~ r2_hidden(F_83,B_85) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_128])).

tff(c_159,plain,(
    ! [E_86,B_87] :
      ( E_86 = B_87
      | ~ r2_hidden(E_86,k1_tarski(B_87)) ) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_162,plain,(
    k2_mcart_1('#skF_7') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_128,c_159])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.18  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_9', type, '#skF_9': $i).
% 1.95/1.18  tff('#skF_8', type, '#skF_8': $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.95/1.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.95/1.18  
% 1.95/1.19  tff(f_66, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.95/1.19  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.95/1.19  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.95/1.19  tff(f_43, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 1.95/1.19  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.95/1.19  tff(c_44, plain, (k2_mcart_1('#skF_7')!='#skF_9' | ~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.19  tff(c_74, plain, (~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_44])).
% 1.95/1.19  tff(c_46, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.19  tff(c_98, plain, (![A_65, B_66, C_67]: (r2_hidden(k1_mcart_1(A_65), B_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.95/1.19  tff(c_100, plain, (r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_46, c_98])).
% 1.95/1.19  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_100])).
% 1.95/1.19  tff(c_105, plain, (k2_mcart_1('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 1.95/1.19  tff(c_125, plain, (![A_73, C_74, B_75]: (r2_hidden(k2_mcart_1(A_73), C_74) | ~r2_hidden(A_73, k2_zfmisc_1(B_75, C_74)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.95/1.19  tff(c_128, plain, (r2_hidden(k2_mcart_1('#skF_7'), k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_125])).
% 1.95/1.19  tff(c_40, plain, (![A_47, B_48]: (k1_mcart_1(k4_tarski(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.19  tff(c_135, plain, (![E_82, F_83, A_84, B_85]: (r2_hidden(k4_tarski(E_82, F_83), k2_zfmisc_1(A_84, B_85)) | ~r2_hidden(F_83, B_85) | ~r2_hidden(E_82, A_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.19  tff(c_38, plain, (![A_44, B_45, C_46]: (k1_mcart_1(A_44)=B_45 | ~r2_hidden(A_44, k2_zfmisc_1(k1_tarski(B_45), C_46)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.19  tff(c_139, plain, (![E_82, F_83, B_45, B_85]: (k1_mcart_1(k4_tarski(E_82, F_83))=B_45 | ~r2_hidden(F_83, B_85) | ~r2_hidden(E_82, k1_tarski(B_45)))), inference(resolution, [status(thm)], [c_135, c_38])).
% 1.95/1.19  tff(c_145, plain, (![E_82, B_45, F_83, B_85]: (E_82=B_45 | ~r2_hidden(F_83, B_85) | ~r2_hidden(E_82, k1_tarski(B_45)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_139])).
% 1.95/1.19  tff(c_150, plain, (![F_83, B_85]: (~r2_hidden(F_83, B_85))), inference(splitLeft, [status(thm)], [c_145])).
% 1.95/1.19  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_128])).
% 1.95/1.19  tff(c_159, plain, (![E_86, B_87]: (E_86=B_87 | ~r2_hidden(E_86, k1_tarski(B_87)))), inference(splitRight, [status(thm)], [c_145])).
% 1.95/1.19  tff(c_162, plain, (k2_mcart_1('#skF_7')='#skF_9'), inference(resolution, [status(thm)], [c_128, c_159])).
% 1.95/1.19  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_162])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 22
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 2
% 1.95/1.19  #Chain   : 0
% 1.99/1.19  #Close   : 0
% 1.99/1.19  
% 1.99/1.19  Ordering : KBO
% 1.99/1.19  
% 1.99/1.19  Simplification rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Subsume      : 5
% 1.99/1.19  #Demod        : 4
% 1.99/1.19  #Tautology    : 17
% 1.99/1.19  #SimpNegUnit  : 8
% 1.99/1.19  #BackRed      : 3
% 1.99/1.19  
% 1.99/1.19  #Partial instantiations: 0
% 1.99/1.19  #Strategies tried      : 1
% 1.99/1.19  
% 1.99/1.19  Timing (in seconds)
% 1.99/1.19  ----------------------
% 1.99/1.19  Preprocessing        : 0.31
% 1.99/1.19  Parsing              : 0.15
% 1.99/1.19  CNF conversion       : 0.02
% 1.99/1.19  Main loop            : 0.13
% 1.99/1.19  Inferencing          : 0.04
% 1.99/1.19  Reduction            : 0.04
% 1.99/1.19  Demodulation         : 0.03
% 1.99/1.19  BG Simplification    : 0.01
% 1.99/1.19  Subsumption          : 0.02
% 1.99/1.19  Abstraction          : 0.01
% 1.99/1.19  MUC search           : 0.00
% 1.99/1.19  Cooper               : 0.00
% 1.99/1.19  Total                : 0.46
% 1.99/1.19  Index Insertion      : 0.00
% 1.99/1.19  Index Deletion       : 0.00
% 1.99/1.19  Index Matching       : 0.00
% 1.99/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
