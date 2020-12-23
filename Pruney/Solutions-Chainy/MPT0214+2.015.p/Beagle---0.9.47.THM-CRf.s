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
% DateTime   : Thu Dec  3 09:47:31 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  89 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_74,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_220,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(B_64) = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_tarski(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_231,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_220])).

tff(c_245,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_52,plain,(
    ! [C_22] : r2_hidden(C_22,k1_tarski(C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_268,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_52])).

tff(c_24,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_109,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_121,plain,(
    ! [B_5] : k3_xboole_0(B_5,B_5) = B_5 ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_156,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_168,plain,(
    ! [B_5] : k5_xboole_0(B_5,B_5) = k4_xboole_0(B_5,B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_156])).

tff(c_311,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r2_hidden(A_77,C_78)
      | ~ r2_hidden(A_77,B_79)
      | ~ r2_hidden(A_77,k5_xboole_0(B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1424,plain,(
    ! [A_2085,B_2086] :
      ( ~ r2_hidden(A_2085,B_2086)
      | ~ r2_hidden(A_2085,B_2086)
      | ~ r2_hidden(A_2085,k4_xboole_0(B_2086,B_2086)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_311])).

tff(c_1435,plain,(
    ! [A_2115] :
      ( ~ r2_hidden(A_2115,k1_xboole_0)
      | ~ r2_hidden(A_2115,k1_xboole_0)
      | ~ r2_hidden(A_2115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1424])).

tff(c_1442,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_268,c_1435])).

tff(c_1448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_1442])).

tff(c_1449,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_1481,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_52])).

tff(c_50,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1492,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1481,c_50])).

tff(c_1496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n020.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 20:23:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.59  
% 3.55/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.59  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.55/1.59  
% 3.55/1.59  %Foreground sorts:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Background operators:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Foreground operators:
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.55/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.55/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.55/1.59  
% 3.55/1.60  tff(f_85, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.55/1.60  tff(f_80, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.55/1.60  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.55/1.60  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.55/1.60  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.60  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.55/1.60  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.55/1.60  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.55/1.60  tff(c_74, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.60  tff(c_76, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.60  tff(c_220, plain, (![B_64, A_65]: (k1_tarski(B_64)=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.60  tff(c_231, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_220])).
% 3.55/1.60  tff(c_245, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_231])).
% 3.55/1.60  tff(c_52, plain, (![C_22]: (r2_hidden(C_22, k1_tarski(C_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.60  tff(c_268, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_245, c_52])).
% 3.55/1.60  tff(c_24, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.60  tff(c_18, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.55/1.60  tff(c_109, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.55/1.60  tff(c_121, plain, (![B_5]: (k3_xboole_0(B_5, B_5)=B_5)), inference(resolution, [status(thm)], [c_18, c_109])).
% 3.55/1.60  tff(c_156, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.60  tff(c_168, plain, (![B_5]: (k5_xboole_0(B_5, B_5)=k4_xboole_0(B_5, B_5))), inference(superposition, [status(thm), theory('equality')], [c_121, c_156])).
% 3.55/1.60  tff(c_311, plain, (![A_77, C_78, B_79]: (~r2_hidden(A_77, C_78) | ~r2_hidden(A_77, B_79) | ~r2_hidden(A_77, k5_xboole_0(B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.60  tff(c_1424, plain, (![A_2085, B_2086]: (~r2_hidden(A_2085, B_2086) | ~r2_hidden(A_2085, B_2086) | ~r2_hidden(A_2085, k4_xboole_0(B_2086, B_2086)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_311])).
% 3.55/1.60  tff(c_1435, plain, (![A_2115]: (~r2_hidden(A_2115, k1_xboole_0) | ~r2_hidden(A_2115, k1_xboole_0) | ~r2_hidden(A_2115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1424])).
% 3.55/1.60  tff(c_1442, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_268, c_1435])).
% 3.55/1.60  tff(c_1448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_1442])).
% 3.55/1.60  tff(c_1449, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_231])).
% 3.55/1.60  tff(c_1481, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_52])).
% 3.55/1.60  tff(c_50, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.60  tff(c_1492, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1481, c_50])).
% 3.55/1.60  tff(c_1496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1492])).
% 3.55/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.60  
% 3.55/1.60  Inference rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Ref     : 0
% 3.55/1.60  #Sup     : 254
% 3.55/1.60  #Fact    : 0
% 3.55/1.60  #Define  : 0
% 3.55/1.60  #Split   : 7
% 3.55/1.60  #Chain   : 0
% 3.55/1.60  #Close   : 0
% 3.55/1.60  
% 3.55/1.60  Ordering : KBO
% 3.55/1.60  
% 3.55/1.60  Simplification rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Subsume      : 19
% 3.55/1.60  #Demod        : 77
% 3.55/1.60  #Tautology    : 132
% 3.55/1.60  #SimpNegUnit  : 1
% 3.55/1.60  #BackRed      : 7
% 3.55/1.60  
% 3.55/1.60  #Partial instantiations: 994
% 3.55/1.60  #Strategies tried      : 1
% 3.55/1.60  
% 3.55/1.60  Timing (in seconds)
% 3.55/1.60  ----------------------
% 3.55/1.60  Preprocessing        : 0.35
% 3.55/1.60  Parsing              : 0.16
% 3.55/1.60  CNF conversion       : 0.03
% 3.55/1.60  Main loop            : 0.51
% 3.55/1.60  Inferencing          : 0.23
% 3.55/1.60  Reduction            : 0.13
% 3.55/1.60  Demodulation         : 0.10
% 3.55/1.60  BG Simplification    : 0.03
% 3.55/1.60  Subsumption          : 0.08
% 3.55/1.61  Abstraction          : 0.02
% 3.55/1.61  MUC search           : 0.00
% 3.55/1.61  Cooper               : 0.00
% 3.55/1.61  Total                : 0.89
% 3.55/1.61  Index Insertion      : 0.00
% 3.55/1.61  Index Deletion       : 0.00
% 3.55/1.61  Index Matching       : 0.00
% 3.55/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
