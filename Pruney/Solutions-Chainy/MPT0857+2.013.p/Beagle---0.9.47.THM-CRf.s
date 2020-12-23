%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  45 expanded)
%              Number of equality atoms :   10 (  14 expanded)
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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

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

tff(c_20,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_43,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    ! [A_28,B_29,C_30] :
      ( r2_hidden(k1_mcart_1(A_28),B_29)
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_88])).

tff(c_93,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_124,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(k2_mcart_1(A_41),C_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_43,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_96,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(k1_tarski(A_31),k1_tarski(B_32)) = k1_tarski(A_31)
      | B_32 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [C_8,B_7] : ~ r2_hidden(C_8,k4_xboole_0(B_7,k1_tarski(C_8))) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [B_32,A_31] :
      ( ~ r2_hidden(B_32,k1_tarski(A_31))
      | B_32 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_130,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_127,c_106])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
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
% 1.81/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.81/1.17  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.81/1.17  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.81/1.17  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.81/1.17  tff(c_20, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.17  tff(c_43, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 1.81/1.17  tff(c_22, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.17  tff(c_86, plain, (![A_28, B_29, C_30]: (r2_hidden(k1_mcart_1(A_28), B_29) | ~r2_hidden(A_28, k2_zfmisc_1(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.17  tff(c_88, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_86])).
% 1.81/1.17  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_88])).
% 1.81/1.17  tff(c_93, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.81/1.17  tff(c_124, plain, (![A_41, C_42, B_43]: (r2_hidden(k2_mcart_1(A_41), C_42) | ~r2_hidden(A_41, k2_zfmisc_1(B_43, C_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.17  tff(c_127, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_124])).
% 1.81/1.17  tff(c_96, plain, (![A_31, B_32]: (k4_xboole_0(k1_tarski(A_31), k1_tarski(B_32))=k1_tarski(A_31) | B_32=A_31)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.81/1.17  tff(c_12, plain, (![C_8, B_7]: (~r2_hidden(C_8, k4_xboole_0(B_7, k1_tarski(C_8))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.17  tff(c_106, plain, (![B_32, A_31]: (~r2_hidden(B_32, k1_tarski(A_31)) | B_32=A_31)), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 1.81/1.17  tff(c_130, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_127, c_106])).
% 1.81/1.17  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_130])).
% 1.81/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  Inference rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Ref     : 0
% 1.81/1.17  #Sup     : 23
% 1.81/1.17  #Fact    : 0
% 1.81/1.17  #Define  : 0
% 1.81/1.17  #Split   : 1
% 1.81/1.17  #Chain   : 0
% 1.81/1.17  #Close   : 0
% 1.81/1.17  
% 1.81/1.17  Ordering : KBO
% 1.81/1.17  
% 1.81/1.17  Simplification rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Subsume      : 0
% 1.81/1.17  #Demod        : 2
% 1.81/1.17  #Tautology    : 16
% 1.81/1.17  #SimpNegUnit  : 2
% 1.81/1.17  #BackRed      : 1
% 1.81/1.17  
% 1.81/1.17  #Partial instantiations: 0
% 1.81/1.17  #Strategies tried      : 1
% 1.81/1.17  
% 1.81/1.17  Timing (in seconds)
% 1.81/1.17  ----------------------
% 1.90/1.18  Preprocessing        : 0.28
% 1.90/1.18  Parsing              : 0.15
% 1.90/1.18  CNF conversion       : 0.02
% 1.90/1.18  Main loop            : 0.13
% 1.90/1.18  Inferencing          : 0.05
% 1.90/1.18  Reduction            : 0.04
% 1.90/1.18  Demodulation         : 0.03
% 1.90/1.18  BG Simplification    : 0.01
% 1.90/1.18  Subsumption          : 0.01
% 1.90/1.18  Abstraction          : 0.01
% 1.90/1.18  MUC search           : 0.00
% 1.90/1.18  Cooper               : 0.00
% 1.90/1.18  Total                : 0.43
% 1.90/1.18  Index Insertion      : 0.00
% 1.90/1.18  Index Deletion       : 0.00
% 1.90/1.18  Index Matching       : 0.00
% 1.90/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
