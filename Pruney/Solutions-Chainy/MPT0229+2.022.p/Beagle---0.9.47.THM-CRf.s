%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:56 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,(
    ! [A_34,B_35] : k2_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_95,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_75])).

tff(c_20,plain,(
    ! [D_13,B_9] : r2_hidden(D_13,k2_tarski(D_13,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_20])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_117,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_110,c_4])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
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
% 1.79/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.79/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.79/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.15  
% 1.87/1.16  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.87/1.16  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.87/1.16  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.87/1.16  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.87/1.16  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.87/1.16  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.16  tff(c_89, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.16  tff(c_44, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.16  tff(c_71, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.16  tff(c_75, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_44, c_71])).
% 1.87/1.16  tff(c_95, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_89, c_75])).
% 1.87/1.16  tff(c_20, plain, (![D_13, B_9]: (r2_hidden(D_13, k2_tarski(D_13, B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.16  tff(c_110, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_20])).
% 1.87/1.16  tff(c_4, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.87/1.16  tff(c_117, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_110, c_4])).
% 1.87/1.16  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_117])).
% 1.87/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  Inference rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Ref     : 0
% 1.87/1.16  #Sup     : 19
% 1.87/1.16  #Fact    : 0
% 1.87/1.16  #Define  : 0
% 1.87/1.16  #Split   : 0
% 1.87/1.16  #Chain   : 0
% 1.87/1.16  #Close   : 0
% 1.87/1.16  
% 1.87/1.16  Ordering : KBO
% 1.87/1.16  
% 1.87/1.16  Simplification rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Subsume      : 0
% 1.87/1.16  #Demod        : 3
% 1.87/1.16  #Tautology    : 14
% 1.87/1.16  #SimpNegUnit  : 1
% 1.87/1.16  #BackRed      : 0
% 1.87/1.16  
% 1.87/1.16  #Partial instantiations: 0
% 1.87/1.16  #Strategies tried      : 1
% 1.87/1.16  
% 1.87/1.16  Timing (in seconds)
% 1.87/1.16  ----------------------
% 1.87/1.16  Preprocessing        : 0.30
% 1.87/1.16  Parsing              : 0.16
% 1.87/1.16  CNF conversion       : 0.02
% 1.87/1.16  Main loop            : 0.10
% 1.87/1.16  Inferencing          : 0.03
% 1.87/1.16  Reduction            : 0.04
% 1.87/1.16  Demodulation         : 0.03
% 1.87/1.16  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.42
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
