%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:57 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  75 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    ! [B_41,A_42] :
      ( k1_tarski(B_41) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_4')
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_112,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [B_22] : ~ r1_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_tarski(B_22) ),
    inference(resolution,[status(thm)],[c_77,c_34])).

tff(c_121,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_85])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2,c_112,c_121])).

tff(c_151,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_10,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_183,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_10])).

tff(c_8,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_183,c_8])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.18  
% 1.70/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.70/1.18  
% 1.70/1.18  %Foreground sorts:
% 1.70/1.18  
% 1.70/1.18  
% 1.70/1.18  %Background operators:
% 1.70/1.18  
% 1.70/1.18  
% 1.70/1.18  %Foreground operators:
% 1.70/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.18  
% 1.93/1.19  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.93/1.19  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.93/1.19  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.93/1.19  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.93/1.19  tff(f_57, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.93/1.19  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.93/1.19  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.19  tff(c_38, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.19  tff(c_96, plain, (![B_41, A_42]: (k1_tarski(B_41)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_41)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.19  tff(c_108, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4') | k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_96])).
% 1.93/1.19  tff(c_112, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_108])).
% 1.93/1.19  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.19  tff(c_77, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k4_xboole_0(A_35, B_36)!=A_35)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.19  tff(c_34, plain, (![B_22]: (~r1_xboole_0(k1_tarski(B_22), k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.19  tff(c_85, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_tarski(B_22))), inference(resolution, [status(thm)], [c_77, c_34])).
% 1.93/1.19  tff(c_121, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_85])).
% 1.93/1.19  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_2, c_112, c_121])).
% 1.93/1.19  tff(c_151, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_108])).
% 1.93/1.19  tff(c_10, plain, (![C_8]: (r2_hidden(C_8, k1_tarski(C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.19  tff(c_183, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_10])).
% 1.93/1.19  tff(c_8, plain, (![C_8, A_4]: (C_8=A_4 | ~r2_hidden(C_8, k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.19  tff(c_199, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_183, c_8])).
% 1.93/1.19  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_199])).
% 1.93/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  Inference rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Ref     : 0
% 1.93/1.19  #Sup     : 39
% 1.93/1.19  #Fact    : 0
% 1.93/1.19  #Define  : 0
% 1.93/1.19  #Split   : 1
% 1.93/1.19  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 5
% 1.93/1.19  #Demod        : 21
% 1.93/1.19  #Tautology    : 20
% 1.93/1.19  #SimpNegUnit  : 1
% 1.93/1.19  #BackRed      : 3
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.19  Preprocessing        : 0.30
% 1.93/1.19  Parsing              : 0.16
% 1.93/1.19  CNF conversion       : 0.02
% 1.93/1.19  Main loop            : 0.14
% 1.93/1.19  Inferencing          : 0.05
% 1.93/1.19  Reduction            : 0.05
% 1.93/1.19  Demodulation         : 0.04
% 1.93/1.19  BG Simplification    : 0.01
% 1.93/1.19  Subsumption          : 0.02
% 1.93/1.19  Abstraction          : 0.01
% 1.93/1.19  MUC search           : 0.00
% 1.93/1.19  Cooper               : 0.00
% 1.93/1.19  Total                : 0.46
% 1.93/1.19  Index Insertion      : 0.00
% 1.93/1.19  Index Deletion       : 0.00
% 1.93/1.19  Index Matching       : 0.00
% 1.93/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
