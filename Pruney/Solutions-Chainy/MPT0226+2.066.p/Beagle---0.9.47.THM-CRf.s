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
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  52 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(k1_tarski(A_33),B_34) = k1_tarski(A_33)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_34])).

tff(c_113,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_116])).

tff(c_121,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [B_17] : ~ r1_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [B_17] : k4_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) != k1_tarski(B_17) ),
    inference(resolution,[status(thm)],[c_73,c_30])).

tff(c_142,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_81])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.92/1.26  
% 1.92/1.26  %Foreground sorts:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Background operators:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Foreground operators:
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.26  
% 1.92/1.26  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.92/1.26  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.92/1.26  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.92/1.26  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.92/1.26  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.92/1.26  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.92/1.26  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.26  tff(c_92, plain, (![A_33, B_34]: (k4_xboole_0(k1_tarski(A_33), B_34)=k1_tarski(A_33) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.26  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.26  tff(c_102, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_34])).
% 1.92/1.26  tff(c_113, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_102])).
% 1.92/1.26  tff(c_10, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.92/1.26  tff(c_116, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_113, c_10])).
% 1.92/1.26  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_116])).
% 1.92/1.26  tff(c_121, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_102])).
% 1.92/1.26  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.26  tff(c_73, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k4_xboole_0(A_28, B_29)!=A_28)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.26  tff(c_30, plain, (![B_17]: (~r1_xboole_0(k1_tarski(B_17), k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.26  tff(c_81, plain, (![B_17]: (k4_xboole_0(k1_tarski(B_17), k1_tarski(B_17))!=k1_tarski(B_17))), inference(resolution, [status(thm)], [c_73, c_30])).
% 1.92/1.26  tff(c_142, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_81])).
% 1.92/1.26  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_4, c_142])).
% 1.92/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  Inference rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Ref     : 0
% 1.92/1.26  #Sup     : 31
% 1.92/1.26  #Fact    : 0
% 1.92/1.26  #Define  : 0
% 1.92/1.26  #Split   : 1
% 1.92/1.26  #Chain   : 0
% 1.92/1.26  #Close   : 0
% 1.92/1.26  
% 1.92/1.27  Ordering : KBO
% 1.92/1.27  
% 1.92/1.27  Simplification rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Subsume      : 0
% 1.92/1.27  #Demod        : 9
% 1.92/1.27  #Tautology    : 19
% 1.92/1.27  #SimpNegUnit  : 1
% 1.92/1.27  #BackRed      : 1
% 1.92/1.27  
% 1.92/1.27  #Partial instantiations: 0
% 1.92/1.27  #Strategies tried      : 1
% 1.92/1.27  
% 1.92/1.27  Timing (in seconds)
% 1.92/1.27  ----------------------
% 1.92/1.27  Preprocessing        : 0.32
% 1.92/1.27  Parsing              : 0.17
% 1.92/1.27  CNF conversion       : 0.02
% 1.92/1.27  Main loop            : 0.13
% 1.92/1.27  Inferencing          : 0.04
% 1.92/1.27  Reduction            : 0.04
% 1.92/1.27  Demodulation         : 0.03
% 1.92/1.27  BG Simplification    : 0.01
% 1.92/1.27  Subsumption          : 0.02
% 1.92/1.27  Abstraction          : 0.01
% 1.92/1.27  MUC search           : 0.00
% 1.92/1.27  Cooper               : 0.00
% 1.92/1.27  Total                : 0.48
% 1.92/1.27  Index Insertion      : 0.00
% 1.92/1.27  Index Deletion       : 0.00
% 1.92/1.27  Index Matching       : 0.00
% 1.92/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
