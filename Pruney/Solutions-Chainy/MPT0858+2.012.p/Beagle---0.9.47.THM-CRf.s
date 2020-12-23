%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   35 (  56 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_22,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k1_mcart_1(A_34),B_35)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_56,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k1_tarski(A_24)
      | B_25 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [C_11,B_10] : ~ r2_hidden(C_11,k4_xboole_0(B_10,k1_tarski(C_11))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [B_25,A_24] :
      ( ~ r2_hidden(B_25,k1_tarski(A_24))
      | B_25 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_103,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_100,c_66])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_103])).

tff(c_108,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_153,plain,(
    ! [A_47,C_48,B_49] :
      ( r2_hidden(k2_mcart_1(A_47),C_48)
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_49,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_153])).

tff(c_135,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(k1_tarski(A_45),k1_tarski(B_46)) = k1_tarski(A_45)
      | B_46 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_157,plain,(
    ! [B_50,A_51] :
      ( ~ r2_hidden(B_50,k1_tarski(A_51))
      | B_50 = A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_14])).

tff(c_160,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_156,c_157])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.21  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.21  
% 1.92/1.21  %Foreground sorts:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Background operators:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Foreground operators:
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.92/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.92/1.21  
% 1.92/1.22  tff(f_56, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.92/1.22  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.92/1.22  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.92/1.22  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.92/1.22  tff(c_22, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.22  tff(c_34, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 1.92/1.22  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.22  tff(c_97, plain, (![A_34, B_35, C_36]: (r2_hidden(k1_mcart_1(A_34), B_35) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.22  tff(c_100, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_97])).
% 1.92/1.22  tff(c_56, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k1_tarski(A_24) | B_25=A_24)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.22  tff(c_14, plain, (![C_11, B_10]: (~r2_hidden(C_11, k4_xboole_0(B_10, k1_tarski(C_11))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.22  tff(c_66, plain, (![B_25, A_24]: (~r2_hidden(B_25, k1_tarski(A_24)) | B_25=A_24)), inference(superposition, [status(thm), theory('equality')], [c_56, c_14])).
% 1.92/1.22  tff(c_103, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_100, c_66])).
% 1.92/1.22  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_103])).
% 1.92/1.22  tff(c_108, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 1.92/1.22  tff(c_153, plain, (![A_47, C_48, B_49]: (r2_hidden(k2_mcart_1(A_47), C_48) | ~r2_hidden(A_47, k2_zfmisc_1(B_49, C_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.22  tff(c_156, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_153])).
% 1.92/1.22  tff(c_135, plain, (![A_45, B_46]: (k4_xboole_0(k1_tarski(A_45), k1_tarski(B_46))=k1_tarski(A_45) | B_46=A_45)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.22  tff(c_157, plain, (![B_50, A_51]: (~r2_hidden(B_50, k1_tarski(A_51)) | B_50=A_51)), inference(superposition, [status(thm), theory('equality')], [c_135, c_14])).
% 1.92/1.22  tff(c_160, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_156, c_157])).
% 1.92/1.22  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_160])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Ref     : 0
% 1.92/1.22  #Sup     : 30
% 1.92/1.22  #Fact    : 0
% 1.92/1.22  #Define  : 0
% 1.92/1.22  #Split   : 1
% 1.92/1.22  #Chain   : 0
% 1.92/1.22  #Close   : 0
% 1.92/1.22  
% 1.92/1.22  Ordering : KBO
% 1.92/1.22  
% 1.92/1.22  Simplification rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Subsume      : 0
% 1.92/1.22  #Demod        : 1
% 1.92/1.22  #Tautology    : 22
% 1.92/1.22  #SimpNegUnit  : 2
% 1.92/1.22  #BackRed      : 1
% 1.92/1.22  
% 1.92/1.22  #Partial instantiations: 0
% 1.92/1.22  #Strategies tried      : 1
% 1.92/1.22  
% 1.92/1.22  Timing (in seconds)
% 1.92/1.22  ----------------------
% 1.92/1.22  Preprocessing        : 0.28
% 1.92/1.22  Parsing              : 0.15
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.13
% 1.92/1.22  Inferencing          : 0.06
% 1.92/1.22  Reduction            : 0.04
% 1.92/1.22  Demodulation         : 0.03
% 1.92/1.22  BG Simplification    : 0.01
% 1.92/1.22  Subsumption          : 0.01
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.44
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
