%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:20 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(c_33,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k3_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_20])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [B_21,A_22] :
      ( k1_tarski(B_21) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [B_25,B_26] :
      ( k3_xboole_0(k1_tarski(B_25),B_26) = k1_tarski(B_25)
      | k3_xboole_0(k1_tarski(B_25),B_26) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_18,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.42  
% 2.01/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.42  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.01/1.42  
% 2.01/1.42  %Foreground sorts:
% 2.01/1.42  
% 2.01/1.42  
% 2.01/1.42  %Background operators:
% 2.01/1.42  
% 2.01/1.42  
% 2.01/1.42  %Foreground operators:
% 2.01/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.42  
% 2.01/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.01/1.43  tff(f_46, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.01/1.43  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.01/1.43  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.01/1.43  tff(c_33, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k3_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.43  tff(c_20, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.43  tff(c_37, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_20])).
% 2.01/1.43  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.43  tff(c_58, plain, (![B_21, A_22]: (k1_tarski(B_21)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.43  tff(c_91, plain, (![B_25, B_26]: (k3_xboole_0(k1_tarski(B_25), B_26)=k1_tarski(B_25) | k3_xboole_0(k1_tarski(B_25), B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_58])).
% 2.01/1.43  tff(c_18, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.43  tff(c_103, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91, c_18])).
% 2.01/1.43  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_103])).
% 2.01/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.43  
% 2.01/1.43  Inference rules
% 2.01/1.43  ----------------------
% 2.01/1.43  #Ref     : 0
% 2.01/1.43  #Sup     : 20
% 2.01/1.43  #Fact    : 1
% 2.01/1.43  #Define  : 0
% 2.01/1.43  #Split   : 0
% 2.01/1.43  #Chain   : 0
% 2.01/1.43  #Close   : 0
% 2.01/1.43  
% 2.01/1.43  Ordering : KBO
% 2.01/1.43  
% 2.01/1.43  Simplification rules
% 2.01/1.43  ----------------------
% 2.01/1.43  #Subsume      : 0
% 2.01/1.43  #Demod        : 1
% 2.01/1.43  #Tautology    : 11
% 2.01/1.43  #SimpNegUnit  : 2
% 2.01/1.43  #BackRed      : 0
% 2.01/1.43  
% 2.01/1.43  #Partial instantiations: 0
% 2.01/1.43  #Strategies tried      : 1
% 2.01/1.43  
% 2.01/1.43  Timing (in seconds)
% 2.01/1.43  ----------------------
% 2.01/1.44  Preprocessing        : 0.46
% 2.01/1.44  Parsing              : 0.23
% 2.01/1.44  CNF conversion       : 0.03
% 2.01/1.44  Main loop            : 0.17
% 2.01/1.44  Inferencing          : 0.07
% 2.01/1.44  Reduction            : 0.05
% 2.01/1.44  Demodulation         : 0.04
% 2.01/1.44  BG Simplification    : 0.01
% 2.01/1.44  Subsumption          : 0.02
% 2.01/1.45  Abstraction          : 0.01
% 2.01/1.45  MUC search           : 0.00
% 2.01/1.45  Cooper               : 0.00
% 2.01/1.45  Total                : 0.66
% 2.01/1.45  Index Insertion      : 0.00
% 2.01/1.45  Index Deletion       : 0.00
% 2.01/1.45  Index Matching       : 0.00
% 2.01/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
