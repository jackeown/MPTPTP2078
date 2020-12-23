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
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  56 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  78 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),B_14)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [C_55,D_56,A_57,B_58] :
      ( ~ r1_xboole_0(C_55,D_56)
      | r1_xboole_0(k2_zfmisc_1(A_57,C_55),k2_zfmisc_1(B_58,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( ~ r1_xboole_0(A_41,B_42)
      | r1_xboole_0(k2_zfmisc_1(A_41,C_43),k2_zfmisc_1(B_42,D_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_103,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_99,c_84])).

tff(c_108,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [D_29,B_30,A_31] :
      ( D_29 = B_30
      | D_29 = A_31
      | ~ r2_hidden(D_29,k2_tarski(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [D_29,A_7] :
      ( D_29 = A_7
      | D_29 = A_7
      | ~ r2_hidden(D_29,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_111,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_108,c_73])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_111])).

tff(c_116,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_136,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_132,c_116])).

tff(c_140,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_144,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_73])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.82/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  
% 2.02/1.23  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 2.02/1.23  tff(f_45, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.02/1.23  tff(f_51, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.02/1.23  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.02/1.23  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.02/1.23  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.23  tff(c_26, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), B_14) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.23  tff(c_132, plain, (![C_55, D_56, A_57, B_58]: (~r1_xboole_0(C_55, D_56) | r1_xboole_0(k2_zfmisc_1(A_57, C_55), k2_zfmisc_1(B_58, D_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.23  tff(c_99, plain, (![A_41, B_42, C_43, D_44]: (~r1_xboole_0(A_41, B_42) | r1_xboole_0(k2_zfmisc_1(A_41, C_43), k2_zfmisc_1(B_42, D_44)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.23  tff(c_32, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.23  tff(c_84, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.02/1.23  tff(c_103, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_99, c_84])).
% 2.02/1.23  tff(c_108, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_103])).
% 2.02/1.23  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.02/1.23  tff(c_64, plain, (![D_29, B_30, A_31]: (D_29=B_30 | D_29=A_31 | ~r2_hidden(D_29, k2_tarski(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.23  tff(c_73, plain, (![D_29, A_7]: (D_29=A_7 | D_29=A_7 | ~r2_hidden(D_29, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_64])).
% 2.02/1.23  tff(c_111, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_108, c_73])).
% 2.02/1.23  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_111])).
% 2.02/1.23  tff(c_116, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_32])).
% 2.02/1.23  tff(c_136, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_132, c_116])).
% 2.02/1.23  tff(c_140, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_136])).
% 2.02/1.23  tff(c_144, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_140, c_73])).
% 2.02/1.23  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_144])).
% 2.02/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 22
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 1
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 0
% 2.02/1.23  #Demod        : 1
% 2.02/1.23  #Tautology    : 12
% 2.02/1.23  #SimpNegUnit  : 2
% 2.02/1.23  #BackRed      : 0
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.02/1.23  Preprocessing        : 0.30
% 2.02/1.23  Parsing              : 0.16
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.13
% 2.02/1.23  Inferencing          : 0.05
% 2.02/1.23  Reduction            : 0.04
% 2.02/1.23  Demodulation         : 0.03
% 2.02/1.23  BG Simplification    : 0.01
% 2.02/1.23  Subsumption          : 0.03
% 2.02/1.23  Abstraction          : 0.01
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.46
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.23  Index Deletion       : 0.00
% 2.02/1.23  Index Matching       : 0.00
% 2.02/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
