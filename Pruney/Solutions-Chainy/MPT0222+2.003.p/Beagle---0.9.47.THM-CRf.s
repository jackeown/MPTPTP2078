%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:16 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_20,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),B_14)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_37,c_18])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_48,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  %$ r2_hidden > r1_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.63/1.17  
% 1.63/1.17  %Foreground sorts:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Background operators:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Foreground operators:
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.63/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.63/1.17  
% 1.63/1.17  tff(f_45, negated_conjecture, ~(![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.63/1.17  tff(f_39, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.63/1.17  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.63/1.17  tff(c_20, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.17  tff(c_37, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), B_14) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.17  tff(c_18, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.17  tff(c_41, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_37, c_18])).
% 1.63/1.17  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.18  tff(c_44, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_41, c_2])).
% 1.63/1.18  tff(c_48, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_44])).
% 1.63/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.18  
% 1.63/1.18  Inference rules
% 1.63/1.18  ----------------------
% 1.63/1.18  #Ref     : 0
% 1.63/1.18  #Sup     : 5
% 1.63/1.18  #Fact    : 0
% 1.63/1.18  #Define  : 0
% 1.63/1.18  #Split   : 0
% 1.63/1.18  #Chain   : 0
% 1.63/1.18  #Close   : 0
% 1.63/1.18  
% 1.63/1.18  Ordering : KBO
% 1.63/1.18  
% 1.63/1.18  Simplification rules
% 1.63/1.18  ----------------------
% 1.63/1.18  #Subsume      : 0
% 1.63/1.18  #Demod        : 0
% 1.63/1.18  #Tautology    : 3
% 1.63/1.18  #SimpNegUnit  : 1
% 1.63/1.18  #BackRed      : 0
% 1.63/1.18  
% 1.63/1.18  #Partial instantiations: 0
% 1.63/1.18  #Strategies tried      : 1
% 1.63/1.18  
% 1.63/1.18  Timing (in seconds)
% 1.63/1.18  ----------------------
% 1.63/1.18  Preprocessing        : 0.25
% 1.63/1.18  Parsing              : 0.13
% 1.63/1.18  CNF conversion       : 0.02
% 1.63/1.18  Main loop            : 0.07
% 1.63/1.18  Inferencing          : 0.02
% 1.63/1.18  Reduction            : 0.02
% 1.63/1.18  Demodulation         : 0.01
% 1.63/1.18  BG Simplification    : 0.01
% 1.63/1.18  Subsumption          : 0.02
% 1.63/1.18  Abstraction          : 0.00
% 1.63/1.18  MUC search           : 0.00
% 1.63/1.18  Cooper               : 0.00
% 1.63/1.18  Total                : 0.34
% 1.63/1.18  Index Insertion      : 0.00
% 1.63/1.18  Index Deletion       : 0.00
% 1.63/1.18  Index Matching       : 0.00
% 1.63/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
