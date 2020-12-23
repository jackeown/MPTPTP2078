%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:54 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  45 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_18,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3')
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_70,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(k1_tarski(A_26),k1_tarski(B_27)) = k1_tarski(A_26)
      | B_27 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ r2_hidden(B_7,A_6)
      | k4_xboole_0(A_6,k1_tarski(B_7)) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [B_28,A_29] :
      ( ~ r2_hidden(B_28,k1_tarski(A_29))
      | B_28 = A_29 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_101,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_68,c_98])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_101])).

tff(c_109,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_170,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_hidden(k2_mcart_1(A_39),C_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_41,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.16  
% 1.81/1.16  %Foreground sorts:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Background operators:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Foreground operators:
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.81/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.81/1.16  
% 1.90/1.17  tff(f_52, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.90/1.17  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.90/1.17  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.90/1.17  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.90/1.17  tff(c_18, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3') | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.17  tff(c_40, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_18])).
% 1.90/1.17  tff(c_20, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.17  tff(c_65, plain, (![A_23, B_24, C_25]: (r2_hidden(k1_mcart_1(A_23), B_24) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.17  tff(c_68, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_65])).
% 1.90/1.17  tff(c_70, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), k1_tarski(B_27))=k1_tarski(A_26) | B_27=A_26)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.17  tff(c_10, plain, (![B_7, A_6]: (~r2_hidden(B_7, A_6) | k4_xboole_0(A_6, k1_tarski(B_7))!=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.17  tff(c_98, plain, (![B_28, A_29]: (~r2_hidden(B_28, k1_tarski(A_29)) | B_28=A_29)), inference(superposition, [status(thm), theory('equality')], [c_70, c_10])).
% 1.90/1.17  tff(c_101, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_68, c_98])).
% 1.90/1.17  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_101])).
% 1.90/1.17  tff(c_109, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 1.90/1.17  tff(c_170, plain, (![A_39, C_40, B_41]: (r2_hidden(k2_mcart_1(A_39), C_40) | ~r2_hidden(A_39, k2_zfmisc_1(B_41, C_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.17  tff(c_172, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_20, c_170])).
% 1.90/1.17  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_172])).
% 1.90/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  Inference rules
% 1.90/1.17  ----------------------
% 1.90/1.17  #Ref     : 0
% 1.90/1.17  #Sup     : 32
% 1.90/1.17  #Fact    : 0
% 1.90/1.17  #Define  : 0
% 1.90/1.17  #Split   : 1
% 1.90/1.17  #Chain   : 0
% 1.90/1.17  #Close   : 0
% 1.90/1.17  
% 1.90/1.17  Ordering : KBO
% 1.90/1.17  
% 1.90/1.17  Simplification rules
% 1.90/1.17  ----------------------
% 1.90/1.17  #Subsume      : 0
% 1.90/1.17  #Demod        : 0
% 1.90/1.17  #Tautology    : 23
% 1.90/1.17  #SimpNegUnit  : 2
% 1.90/1.17  #BackRed      : 0
% 1.90/1.17  
% 1.90/1.17  #Partial instantiations: 0
% 1.90/1.17  #Strategies tried      : 1
% 1.90/1.17  
% 1.90/1.17  Timing (in seconds)
% 1.90/1.17  ----------------------
% 1.90/1.17  Preprocessing        : 0.28
% 1.90/1.17  Parsing              : 0.15
% 1.90/1.17  CNF conversion       : 0.02
% 1.90/1.17  Main loop            : 0.14
% 1.90/1.17  Inferencing          : 0.06
% 1.90/1.17  Reduction            : 0.04
% 1.90/1.17  Demodulation         : 0.02
% 1.90/1.17  BG Simplification    : 0.01
% 1.90/1.17  Subsumption          : 0.02
% 1.90/1.17  Abstraction          : 0.01
% 1.90/1.17  MUC search           : 0.00
% 1.90/1.17  Cooper               : 0.00
% 1.90/1.17  Total                : 0.45
% 1.90/1.17  Index Insertion      : 0.00
% 1.90/1.17  Index Deletion       : 0.00
% 1.90/1.17  Index Matching       : 0.00
% 1.90/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
