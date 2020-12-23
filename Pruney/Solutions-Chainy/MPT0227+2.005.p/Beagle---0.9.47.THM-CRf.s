%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:50 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    3
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_8,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(k1_tarski(A_26),B_27) = k1_xboole_0
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_3',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_30])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.63/1.11  
% 1.63/1.11  %Foreground sorts:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Background operators:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Foreground operators:
% 1.63/1.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.63/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.63/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.11  
% 1.63/1.12  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.63/1.12  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.63/1.12  tff(f_47, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.63/1.12  tff(c_8, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.63/1.12  tff(c_69, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), B_27)=k1_xboole_0 | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.12  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_3', '#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.63/1.12  tff(c_78, plain, (~r2_hidden('#skF_3', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_30])).
% 1.63/1.12  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 1.63/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  Inference rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Ref     : 0
% 1.63/1.12  #Sup     : 12
% 1.63/1.12  #Fact    : 0
% 1.63/1.12  #Define  : 0
% 1.63/1.12  #Split   : 0
% 1.63/1.12  #Chain   : 0
% 1.63/1.12  #Close   : 0
% 1.63/1.12  
% 1.63/1.12  Ordering : KBO
% 1.63/1.12  
% 1.63/1.12  Simplification rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Subsume      : 0
% 1.63/1.12  #Demod        : 2
% 1.63/1.12  #Tautology    : 9
% 1.63/1.12  #SimpNegUnit  : 0
% 1.63/1.12  #BackRed      : 0
% 1.63/1.12  
% 1.63/1.12  #Partial instantiations: 0
% 1.63/1.12  #Strategies tried      : 1
% 1.63/1.12  
% 1.63/1.12  Timing (in seconds)
% 1.63/1.12  ----------------------
% 1.63/1.12  Preprocessing        : 0.28
% 1.63/1.12  Parsing              : 0.14
% 1.63/1.12  CNF conversion       : 0.02
% 1.63/1.12  Main loop            : 0.08
% 1.63/1.12  Inferencing          : 0.03
% 1.63/1.12  Reduction            : 0.03
% 1.63/1.12  Demodulation         : 0.02
% 1.63/1.12  BG Simplification    : 0.01
% 1.63/1.12  Subsumption          : 0.02
% 1.63/1.12  Abstraction          : 0.01
% 1.63/1.12  MUC search           : 0.00
% 1.63/1.12  Cooper               : 0.00
% 1.63/1.12  Total                : 0.38
% 1.63/1.12  Index Insertion      : 0.00
% 1.63/1.12  Index Deletion       : 0.00
% 1.63/1.12  Index Matching       : 0.00
% 1.63/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
