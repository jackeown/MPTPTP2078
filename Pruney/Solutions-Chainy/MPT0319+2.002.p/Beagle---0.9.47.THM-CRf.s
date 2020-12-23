%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:10 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  56 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_26,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),B_10)
      | r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [C_13,D_14,A_11,B_12] :
      ( ~ r1_xboole_0(C_13,D_14)
      | r1_xboole_0(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( ~ r1_xboole_0(A_11,B_12)
      | r1_xboole_0(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_64,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_68,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_71])).

tff(c_76,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_84,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_89,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_92,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.83/1.18  
% 1.83/1.18  %Foreground sorts:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Background operators:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Foreground operators:
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.83/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.18  
% 1.83/1.19  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 1.83/1.19  tff(f_41, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.83/1.19  tff(f_47, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.83/1.19  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.83/1.19  tff(c_26, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.19  tff(c_18, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), B_10) | r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.19  tff(c_20, plain, (![C_13, D_14, A_11, B_12]: (~r1_xboole_0(C_13, D_14) | r1_xboole_0(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, D_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.19  tff(c_22, plain, (![A_11, B_12, C_13, D_14]: (~r1_xboole_0(A_11, B_12) | r1_xboole_0(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, D_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.19  tff(c_24, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.19  tff(c_56, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_24])).
% 1.83/1.19  tff(c_64, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_56])).
% 1.83/1.19  tff(c_68, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_64])).
% 1.83/1.19  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_71, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_68, c_2])).
% 1.83/1.19  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_71])).
% 1.83/1.19  tff(c_76, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_24])).
% 1.83/1.19  tff(c_84, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_76])).
% 1.83/1.19  tff(c_89, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_84])).
% 1.83/1.19  tff(c_92, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_89, c_2])).
% 1.83/1.19  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_92])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 13
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 1
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 0
% 1.83/1.19  #Demod        : 0
% 1.83/1.19  #Tautology    : 5
% 1.83/1.19  #SimpNegUnit  : 2
% 1.83/1.19  #BackRed      : 0
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.90/1.20  Preprocessing        : 0.29
% 1.90/1.20  Parsing              : 0.16
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.11
% 1.90/1.20  Inferencing          : 0.04
% 1.90/1.20  Reduction            : 0.03
% 1.90/1.20  Demodulation         : 0.02
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.02
% 1.90/1.20  Abstraction          : 0.00
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.42
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
