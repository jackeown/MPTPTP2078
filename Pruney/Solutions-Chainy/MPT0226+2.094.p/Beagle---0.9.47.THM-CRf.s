%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:49 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   32 (  57 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  77 expanded)
%              Number of equality atoms :   21 (  55 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),k1_tarski(B_23))
      | B_23 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = A_2
      | ~ r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),k1_tarski(B_31)) = k1_tarski(A_30)
      | B_31 = A_30 ) ),
    inference(resolution,[status(thm)],[c_63,c_6])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_22])).

tff(c_135,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_123])).

tff(c_2,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_43,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [B_11] : ~ r1_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    ! [B_11] : k4_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) != k1_tarski(B_11) ),
    inference(resolution,[status(thm)],[c_43,c_16])).

tff(c_148,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_51])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_62,c_135,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.14  
% 1.77/1.14  %Foreground sorts:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Background operators:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Foreground operators:
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.14  
% 1.77/1.15  tff(f_62, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.77/1.15  tff(f_57, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.77/1.15  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.77/1.15  tff(f_37, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.77/1.15  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.77/1.15  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.15  tff(c_63, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), k1_tarski(B_23)) | B_23=A_22)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.77/1.15  tff(c_6, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=A_2 | ~r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.15  tff(c_109, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), k1_tarski(B_31))=k1_tarski(A_30) | B_31=A_30)), inference(resolution, [status(thm)], [c_63, c_6])).
% 1.77/1.15  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.77/1.15  tff(c_123, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_109, c_22])).
% 1.77/1.15  tff(c_135, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_123])).
% 1.77/1.15  tff(c_2, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.15  tff(c_54, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.15  tff(c_62, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_54])).
% 1.77/1.15  tff(c_43, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.15  tff(c_16, plain, (![B_11]: (~r1_xboole_0(k1_tarski(B_11), k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.15  tff(c_51, plain, (![B_11]: (k4_xboole_0(k1_tarski(B_11), k1_tarski(B_11))!=k1_tarski(B_11))), inference(resolution, [status(thm)], [c_43, c_16])).
% 1.77/1.15  tff(c_148, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_135, c_51])).
% 1.77/1.15  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_62, c_135, c_148])).
% 1.77/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  Inference rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Ref     : 0
% 1.77/1.15  #Sup     : 35
% 1.77/1.15  #Fact    : 0
% 1.77/1.15  #Define  : 0
% 1.77/1.15  #Split   : 0
% 1.77/1.15  #Chain   : 0
% 1.77/1.15  #Close   : 0
% 1.77/1.15  
% 1.77/1.15  Ordering : KBO
% 1.77/1.15  
% 1.77/1.15  Simplification rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Subsume      : 0
% 1.77/1.15  #Demod        : 5
% 1.77/1.15  #Tautology    : 20
% 1.77/1.15  #SimpNegUnit  : 2
% 1.77/1.15  #BackRed      : 1
% 1.77/1.15  
% 1.77/1.15  #Partial instantiations: 0
% 1.77/1.15  #Strategies tried      : 1
% 1.77/1.15  
% 1.77/1.15  Timing (in seconds)
% 1.77/1.15  ----------------------
% 1.77/1.15  Preprocessing        : 0.28
% 1.77/1.15  Parsing              : 0.15
% 1.77/1.15  CNF conversion       : 0.01
% 1.77/1.15  Main loop            : 0.11
% 1.77/1.15  Inferencing          : 0.05
% 1.77/1.15  Reduction            : 0.03
% 1.77/1.15  Demodulation         : 0.02
% 1.77/1.15  BG Simplification    : 0.01
% 1.77/1.15  Subsumption          : 0.01
% 1.77/1.15  Abstraction          : 0.01
% 1.77/1.15  MUC search           : 0.00
% 1.77/1.15  Cooper               : 0.00
% 1.77/1.15  Total                : 0.41
% 1.77/1.15  Index Insertion      : 0.00
% 1.77/1.15  Index Deletion       : 0.00
% 1.77/1.15  Index Matching       : 0.00
% 1.77/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
