%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_48])).

tff(c_63,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),k1_tarski(B_31)) = k1_tarski(A_30)
      | B_31 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [C_8,B_7] : ~ r2_hidden(C_8,k4_xboole_0(B_7,k1_tarski(C_8))) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [B_32,A_33] :
      ( ~ r2_hidden(B_32,k1_tarski(A_33))
      | B_32 = A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_87,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_51,c_84])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_87])).

tff(c_92,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_119,plain,(
    ! [A_48,C_49,B_50] :
      ( k2_mcart_1(A_48) = C_49
      | ~ r2_hidden(A_48,k2_zfmisc_1(B_50,k1_tarski(C_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.22  
% 1.76/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.22  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.22  
% 1.76/1.22  %Foreground sorts:
% 1.76/1.22  
% 1.76/1.22  
% 1.76/1.22  %Background operators:
% 1.76/1.22  
% 1.76/1.22  
% 1.76/1.22  %Foreground operators:
% 1.76/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.22  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.76/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.22  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.76/1.22  
% 1.93/1.23  tff(f_60, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.93/1.23  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.93/1.23  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.93/1.23  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.93/1.23  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.93/1.23  tff(c_24, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.23  tff(c_36, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 1.93/1.23  tff(c_26, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.23  tff(c_48, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.23  tff(c_51, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_48])).
% 1.93/1.23  tff(c_63, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), k1_tarski(B_31))=k1_tarski(A_30) | B_31=A_30)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.23  tff(c_12, plain, (![C_8, B_7]: (~r2_hidden(C_8, k4_xboole_0(B_7, k1_tarski(C_8))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.23  tff(c_84, plain, (![B_32, A_33]: (~r2_hidden(B_32, k1_tarski(A_33)) | B_32=A_33)), inference(superposition, [status(thm), theory('equality')], [c_63, c_12])).
% 1.93/1.23  tff(c_87, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_51, c_84])).
% 1.93/1.23  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_87])).
% 1.93/1.23  tff(c_92, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 1.93/1.23  tff(c_119, plain, (![A_48, C_49, B_50]: (k2_mcart_1(A_48)=C_49 | ~r2_hidden(A_48, k2_zfmisc_1(B_50, k1_tarski(C_49))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.23  tff(c_122, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_119])).
% 1.93/1.23  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_122])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 21
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 1
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 1
% 1.93/1.23  #Demod        : 1
% 1.93/1.23  #Tautology    : 14
% 1.93/1.23  #SimpNegUnit  : 2
% 1.93/1.23  #BackRed      : 0
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 1.93/1.23  Preprocessing        : 0.30
% 1.93/1.23  Parsing              : 0.16
% 1.93/1.23  CNF conversion       : 0.02
% 1.93/1.23  Main loop            : 0.12
% 1.93/1.23  Inferencing          : 0.05
% 1.93/1.23  Reduction            : 0.04
% 1.93/1.23  Demodulation         : 0.02
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.02
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.45
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
