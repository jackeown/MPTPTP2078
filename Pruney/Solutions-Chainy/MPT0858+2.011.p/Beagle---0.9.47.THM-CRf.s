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
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   17 (  25 expanded)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_45,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(c_22,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_hidden(k1_mcart_1(A_29),B_30)
      | ~ r2_hidden(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_84,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(k1_tarski(A_32),k1_tarski(B_33)) = k1_tarski(A_32)
      | B_33 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ r2_hidden(B_7,A_6)
      | k4_xboole_0(A_6,k1_tarski(B_7)) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [B_34,A_35] :
      ( ~ r2_hidden(B_34,k1_tarski(A_35))
      | B_34 = A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_115,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_82,c_112])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_115])).

tff(c_123,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_188,plain,(
    ! [A_46,C_47,B_48] :
      ( k2_mcart_1(A_46) = C_47
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_48,k1_tarski(C_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_191,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_188])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.15  
% 1.79/1.15  %Foreground sorts:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Background operators:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Foreground operators:
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.15  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.79/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.15  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.79/1.15  
% 1.79/1.16  tff(f_58, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.79/1.16  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.79/1.16  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.79/1.16  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.79/1.16  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.79/1.16  tff(c_22, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.16  tff(c_34, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 1.79/1.16  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.16  tff(c_79, plain, (![A_29, B_30, C_31]: (r2_hidden(k1_mcart_1(A_29), B_30) | ~r2_hidden(A_29, k2_zfmisc_1(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.16  tff(c_82, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_79])).
% 1.79/1.16  tff(c_84, plain, (![A_32, B_33]: (k4_xboole_0(k1_tarski(A_32), k1_tarski(B_33))=k1_tarski(A_32) | B_33=A_32)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.79/1.16  tff(c_10, plain, (![B_7, A_6]: (~r2_hidden(B_7, A_6) | k4_xboole_0(A_6, k1_tarski(B_7))!=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.16  tff(c_112, plain, (![B_34, A_35]: (~r2_hidden(B_34, k1_tarski(A_35)) | B_34=A_35)), inference(superposition, [status(thm), theory('equality')], [c_84, c_10])).
% 1.79/1.16  tff(c_115, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_82, c_112])).
% 1.79/1.16  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_115])).
% 1.79/1.16  tff(c_123, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 1.79/1.16  tff(c_188, plain, (![A_46, C_47, B_48]: (k2_mcart_1(A_46)=C_47 | ~r2_hidden(A_46, k2_zfmisc_1(B_48, k1_tarski(C_47))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.79/1.16  tff(c_191, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_24, c_188])).
% 1.79/1.16  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_191])).
% 1.79/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  Inference rules
% 1.79/1.16  ----------------------
% 1.79/1.16  #Ref     : 0
% 1.79/1.16  #Sup     : 36
% 1.79/1.16  #Fact    : 0
% 1.79/1.16  #Define  : 0
% 1.79/1.16  #Split   : 1
% 1.79/1.16  #Chain   : 0
% 1.79/1.16  #Close   : 0
% 1.79/1.16  
% 1.79/1.16  Ordering : KBO
% 1.79/1.16  
% 1.79/1.16  Simplification rules
% 1.79/1.16  ----------------------
% 1.79/1.16  #Subsume      : 1
% 1.79/1.16  #Demod        : 2
% 1.79/1.16  #Tautology    : 27
% 1.79/1.16  #SimpNegUnit  : 2
% 1.79/1.16  #BackRed      : 0
% 1.79/1.16  
% 1.79/1.16  #Partial instantiations: 0
% 1.79/1.16  #Strategies tried      : 1
% 1.79/1.16  
% 1.79/1.16  Timing (in seconds)
% 1.79/1.16  ----------------------
% 1.88/1.17  Preprocessing        : 0.28
% 1.88/1.17  Parsing              : 0.15
% 1.88/1.17  CNF conversion       : 0.02
% 1.88/1.17  Main loop            : 0.13
% 1.88/1.17  Inferencing          : 0.05
% 1.88/1.17  Reduction            : 0.03
% 1.88/1.17  Demodulation         : 0.02
% 1.88/1.17  BG Simplification    : 0.01
% 1.88/1.17  Subsumption          : 0.02
% 1.88/1.17  Abstraction          : 0.01
% 1.88/1.17  MUC search           : 0.00
% 1.88/1.17  Cooper               : 0.00
% 1.88/1.17  Total                : 0.43
% 1.88/1.17  Index Insertion      : 0.00
% 1.88/1.17  Index Deletion       : 0.00
% 1.88/1.17  Index Matching       : 0.00
% 1.88/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
