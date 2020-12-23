%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:54 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  45 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_16,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3')
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_18,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_12),B_13)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_22])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(k1_tarski(A_21),k1_tarski(B_22)) = k1_tarski(A_21)
      | B_22 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [C_5,B_4] : ~ r2_hidden(C_5,k4_xboole_0(B_4,k1_tarski(C_5))) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [B_23,A_24] :
      ( ~ r2_hidden(B_23,k1_tarski(A_24))
      | B_23 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_56,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_25,c_53])).

tff(c_60,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_56])).

tff(c_61,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_74,plain,(
    ! [A_32,C_33,B_34] :
      ( r2_hidden(k2_mcart_1(A_32),C_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_34,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  %$ r2_hidden > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.16  
% 1.75/1.16  %Foreground sorts:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Background operators:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Foreground operators:
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.75/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.75/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.75/1.16  
% 1.75/1.17  tff(f_50, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.75/1.17  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.75/1.17  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.75/1.17  tff(f_37, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.75/1.17  tff(c_16, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3') | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.17  tff(c_20, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 1.75/1.17  tff(c_18, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.17  tff(c_22, plain, (![A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(A_12), B_13) | ~r2_hidden(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.17  tff(c_25, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_22])).
% 1.75/1.17  tff(c_32, plain, (![A_21, B_22]: (k4_xboole_0(k1_tarski(A_21), k1_tarski(B_22))=k1_tarski(A_21) | B_22=A_21)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.75/1.17  tff(c_8, plain, (![C_5, B_4]: (~r2_hidden(C_5, k4_xboole_0(B_4, k1_tarski(C_5))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.17  tff(c_53, plain, (![B_23, A_24]: (~r2_hidden(B_23, k1_tarski(A_24)) | B_23=A_24)), inference(superposition, [status(thm), theory('equality')], [c_32, c_8])).
% 1.75/1.17  tff(c_56, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_25, c_53])).
% 1.75/1.17  tff(c_60, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_56])).
% 1.75/1.17  tff(c_61, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_16])).
% 1.75/1.17  tff(c_74, plain, (![A_32, C_33, B_34]: (r2_hidden(k2_mcart_1(A_32), C_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_34, C_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.17  tff(c_76, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_18, c_74])).
% 1.75/1.17  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_76])).
% 1.75/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.17  
% 1.75/1.17  Inference rules
% 1.75/1.17  ----------------------
% 1.75/1.17  #Ref     : 0
% 1.75/1.17  #Sup     : 12
% 1.75/1.17  #Fact    : 0
% 1.75/1.17  #Define  : 0
% 1.75/1.17  #Split   : 1
% 1.75/1.17  #Chain   : 0
% 1.75/1.17  #Close   : 0
% 1.75/1.17  
% 1.75/1.17  Ordering : KBO
% 1.75/1.17  
% 1.75/1.17  Simplification rules
% 1.75/1.17  ----------------------
% 1.75/1.17  #Subsume      : 0
% 1.75/1.17  #Demod        : 1
% 1.75/1.17  #Tautology    : 6
% 1.75/1.17  #SimpNegUnit  : 2
% 1.75/1.17  #BackRed      : 0
% 1.75/1.17  
% 1.75/1.17  #Partial instantiations: 0
% 1.75/1.17  #Strategies tried      : 1
% 1.75/1.17  
% 1.75/1.17  Timing (in seconds)
% 1.75/1.17  ----------------------
% 1.75/1.17  Preprocessing        : 0.26
% 1.75/1.17  Parsing              : 0.15
% 1.75/1.17  CNF conversion       : 0.02
% 1.75/1.17  Main loop            : 0.10
% 1.75/1.17  Inferencing          : 0.04
% 1.75/1.17  Reduction            : 0.03
% 1.75/1.17  Demodulation         : 0.01
% 1.75/1.17  BG Simplification    : 0.01
% 1.75/1.17  Subsumption          : 0.01
% 1.75/1.17  Abstraction          : 0.00
% 1.75/1.17  MUC search           : 0.00
% 1.75/1.17  Cooper               : 0.00
% 1.75/1.17  Total                : 0.39
% 1.75/1.17  Index Insertion      : 0.00
% 1.75/1.17  Index Deletion       : 0.00
% 1.75/1.17  Index Matching       : 0.00
% 1.75/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
