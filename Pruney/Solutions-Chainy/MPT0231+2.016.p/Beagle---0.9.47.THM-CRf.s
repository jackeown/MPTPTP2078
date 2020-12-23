%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  63 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_70,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_219,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(B_72) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_tarski(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_235,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_219])).

tff(c_260,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_66,plain,(
    ! [A_32,B_33] : r1_tarski(k1_tarski(A_32),k2_tarski(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_272,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_66])).

tff(c_162,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_180,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_282,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_272,c_180])).

tff(c_68,plain,(
    ! [B_35,A_34] :
      ( B_35 = A_34
      | ~ r1_tarski(k1_tarski(A_34),k1_tarski(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_294,plain,(
    ! [B_35] :
      ( B_35 = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_68])).

tff(c_312,plain,(
    ! [B_79] : B_79 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_294])).

tff(c_390,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_70])).

tff(c_391,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_416,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_66])).

tff(c_429,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_416,c_68])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.40  
% 2.22/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.40  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.22/1.40  
% 2.22/1.40  %Foreground sorts:
% 2.22/1.40  
% 2.22/1.40  
% 2.22/1.40  %Background operators:
% 2.22/1.40  
% 2.22/1.40  
% 2.22/1.40  %Foreground operators:
% 2.22/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.22/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.22/1.40  
% 2.22/1.41  tff(f_86, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.22/1.41  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.41  tff(f_75, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.22/1.41  tff(f_77, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.22/1.41  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.41  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.22/1.41  tff(c_70, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.22/1.41  tff(c_24, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.41  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.22/1.41  tff(c_219, plain, (![B_72, A_73]: (k1_tarski(B_72)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_tarski(B_72)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.41  tff(c_235, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_219])).
% 2.22/1.41  tff(c_260, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_235])).
% 2.22/1.41  tff(c_66, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), k2_tarski(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.22/1.41  tff(c_272, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_260, c_66])).
% 2.22/1.41  tff(c_162, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.22/1.41  tff(c_180, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_162])).
% 2.22/1.41  tff(c_282, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_272, c_180])).
% 2.22/1.41  tff(c_68, plain, (![B_35, A_34]: (B_35=A_34 | ~r1_tarski(k1_tarski(A_34), k1_tarski(B_35)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.22/1.41  tff(c_294, plain, (![B_35]: (B_35='#skF_3' | ~r1_tarski(k1_xboole_0, k1_tarski(B_35)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_68])).
% 2.22/1.41  tff(c_312, plain, (![B_79]: (B_79='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_294])).
% 2.22/1.41  tff(c_390, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_312, c_70])).
% 2.22/1.41  tff(c_391, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_235])).
% 2.22/1.41  tff(c_416, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_391, c_66])).
% 2.22/1.41  tff(c_429, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_416, c_68])).
% 2.22/1.41  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_429])).
% 2.22/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  
% 2.22/1.41  Inference rules
% 2.22/1.41  ----------------------
% 2.22/1.41  #Ref     : 0
% 2.22/1.41  #Sup     : 99
% 2.22/1.41  #Fact    : 0
% 2.22/1.41  #Define  : 0
% 2.22/1.41  #Split   : 1
% 2.22/1.41  #Chain   : 0
% 2.22/1.41  #Close   : 0
% 2.22/1.41  
% 2.22/1.41  Ordering : KBO
% 2.22/1.41  
% 2.22/1.41  Simplification rules
% 2.22/1.41  ----------------------
% 2.22/1.41  #Subsume      : 11
% 2.22/1.41  #Demod        : 29
% 2.22/1.41  #Tautology    : 46
% 2.22/1.41  #SimpNegUnit  : 1
% 2.22/1.41  #BackRed      : 4
% 2.22/1.41  
% 2.22/1.41  #Partial instantiations: 30
% 2.22/1.41  #Strategies tried      : 1
% 2.22/1.41  
% 2.22/1.41  Timing (in seconds)
% 2.22/1.41  ----------------------
% 2.22/1.41  Preprocessing        : 0.30
% 2.22/1.41  Parsing              : 0.15
% 2.22/1.41  CNF conversion       : 0.02
% 2.22/1.41  Main loop            : 0.24
% 2.22/1.41  Inferencing          : 0.09
% 2.22/1.41  Reduction            : 0.07
% 2.22/1.41  Demodulation         : 0.05
% 2.22/1.41  BG Simplification    : 0.02
% 2.22/1.41  Subsumption          : 0.05
% 2.22/1.41  Abstraction          : 0.01
% 2.22/1.41  MUC search           : 0.00
% 2.22/1.41  Cooper               : 0.00
% 2.22/1.41  Total                : 0.56
% 2.22/1.41  Index Insertion      : 0.00
% 2.22/1.42  Index Deletion       : 0.00
% 2.22/1.42  Index Matching       : 0.00
% 2.22/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
