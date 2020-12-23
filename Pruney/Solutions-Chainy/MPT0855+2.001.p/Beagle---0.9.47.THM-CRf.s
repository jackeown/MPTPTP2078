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
% DateTime   : Thu Dec  3 10:08:51 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  54 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) )
       => ( ! [D,E] : A != k4_tarski(D,E)
          | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_32,plain,(
    k4_tarski('#skF_10','#skF_11') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [A_41,B_42] : k1_mcart_1(k4_tarski(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    k1_mcart_1('#skF_7') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_53])).

tff(c_36,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_41,plain,(
    ! [A_39,B_40] : k2_mcart_1(k4_tarski(A_39,B_40)) = B_40 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    k2_mcart_1('#skF_7') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_41])).

tff(c_34,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    r2_hidden('#skF_11','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34])).

tff(c_75,plain,(
    ! [E_43,F_44,A_45,B_46] :
      ( r2_hidden(k4_tarski(E_43,F_44),k2_zfmisc_1(A_45,B_46))
      | ~ r2_hidden(F_44,B_46)
      | ~ r2_hidden(E_43,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_7',k2_zfmisc_1(A_47,B_48))
      | ~ r2_hidden('#skF_11',B_48)
      | ~ r2_hidden('#skF_10',A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,
    ( ~ r2_hidden('#skF_11','#skF_9')
    | ~ r2_hidden('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_79,c_30])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_65,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.12  tff('#skF_11', type, '#skF_11': $i).
% 1.64/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.64/1.12  tff('#skF_7', type, '#skF_7': $i).
% 1.64/1.12  tff('#skF_10', type, '#skF_10': $i).
% 1.64/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.64/1.12  tff('#skF_9', type, '#skF_9': $i).
% 1.64/1.12  tff('#skF_8', type, '#skF_8': $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.64/1.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.64/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.64/1.12  
% 1.64/1.13  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 1.64/1.13  tff(f_41, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.64/1.13  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 1.64/1.13  tff(c_32, plain, (k4_tarski('#skF_10', '#skF_11')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.13  tff(c_53, plain, (![A_41, B_42]: (k1_mcart_1(k4_tarski(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.13  tff(c_62, plain, (k1_mcart_1('#skF_7')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_32, c_53])).
% 1.64/1.13  tff(c_36, plain, (r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.13  tff(c_70, plain, (r2_hidden('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 1.64/1.13  tff(c_41, plain, (![A_39, B_40]: (k2_mcart_1(k4_tarski(A_39, B_40))=B_40)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.13  tff(c_50, plain, (k2_mcart_1('#skF_7')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_32, c_41])).
% 1.64/1.13  tff(c_34, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.13  tff(c_65, plain, (r2_hidden('#skF_11', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34])).
% 1.64/1.13  tff(c_75, plain, (![E_43, F_44, A_45, B_46]: (r2_hidden(k4_tarski(E_43, F_44), k2_zfmisc_1(A_45, B_46)) | ~r2_hidden(F_44, B_46) | ~r2_hidden(E_43, A_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.13  tff(c_79, plain, (![A_47, B_48]: (r2_hidden('#skF_7', k2_zfmisc_1(A_47, B_48)) | ~r2_hidden('#skF_11', B_48) | ~r2_hidden('#skF_10', A_47))), inference(superposition, [status(thm), theory('equality')], [c_32, c_75])).
% 1.64/1.13  tff(c_30, plain, (~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.13  tff(c_82, plain, (~r2_hidden('#skF_11', '#skF_9') | ~r2_hidden('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_79, c_30])).
% 1.64/1.13  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_65, c_82])).
% 1.64/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  Inference rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Ref     : 0
% 1.64/1.13  #Sup     : 14
% 1.64/1.13  #Fact    : 0
% 1.64/1.13  #Define  : 0
% 1.64/1.13  #Split   : 0
% 1.64/1.13  #Chain   : 0
% 1.64/1.13  #Close   : 0
% 1.64/1.13  
% 1.64/1.13  Ordering : KBO
% 1.64/1.13  
% 1.64/1.13  Simplification rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Subsume      : 0
% 1.64/1.13  #Demod        : 4
% 1.64/1.13  #Tautology    : 10
% 1.64/1.13  #SimpNegUnit  : 0
% 1.64/1.13  #BackRed      : 2
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.28
% 1.64/1.13  Parsing              : 0.14
% 1.64/1.13  CNF conversion       : 0.03
% 1.64/1.13  Main loop            : 0.09
% 1.64/1.13  Inferencing          : 0.03
% 1.64/1.13  Reduction            : 0.03
% 1.64/1.13  Demodulation         : 0.02
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.02
% 1.64/1.13  Abstraction          : 0.01
% 1.75/1.13  MUC search           : 0.00
% 1.75/1.13  Cooper               : 0.00
% 1.75/1.13  Total                : 0.40
% 1.75/1.13  Index Insertion      : 0.00
% 1.75/1.13  Index Deletion       : 0.00
% 1.75/1.13  Index Matching       : 0.00
% 1.75/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
