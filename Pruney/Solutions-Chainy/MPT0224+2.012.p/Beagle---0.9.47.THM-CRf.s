%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:30 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(k1_tarski(A_4),k2_tarski(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_4,B_5] : k3_xboole_0(k1_tarski(A_4),k2_tarski(A_4,B_5)) = k1_tarski(A_4) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_8,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.07  
% 1.50/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.07  %$ r1_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.50/1.07  
% 1.50/1.07  %Foreground sorts:
% 1.50/1.07  
% 1.50/1.07  
% 1.50/1.07  %Background operators:
% 1.50/1.07  
% 1.50/1.07  
% 1.50/1.07  %Foreground operators:
% 1.50/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.50/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.50/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.50/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.50/1.07  
% 1.50/1.08  tff(f_33, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.50/1.08  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.50/1.08  tff(f_36, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.50/1.08  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), k2_tarski(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.50/1.08  tff(c_23, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.08  tff(c_31, plain, (![A_4, B_5]: (k3_xboole_0(k1_tarski(A_4), k2_tarski(A_4, B_5))=k1_tarski(A_4))), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.50/1.08  tff(c_8, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.50/1.08  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_8])).
% 1.50/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.08  
% 1.50/1.08  Inference rules
% 1.50/1.08  ----------------------
% 1.50/1.08  #Ref     : 0
% 1.50/1.08  #Sup     : 7
% 1.50/1.08  #Fact    : 0
% 1.50/1.08  #Define  : 0
% 1.50/1.08  #Split   : 0
% 1.50/1.08  #Chain   : 0
% 1.50/1.08  #Close   : 0
% 1.50/1.08  
% 1.50/1.08  Ordering : KBO
% 1.50/1.08  
% 1.50/1.08  Simplification rules
% 1.50/1.08  ----------------------
% 1.50/1.08  #Subsume      : 0
% 1.50/1.08  #Demod        : 1
% 1.50/1.08  #Tautology    : 4
% 1.50/1.08  #SimpNegUnit  : 0
% 1.50/1.08  #BackRed      : 1
% 1.50/1.08  
% 1.50/1.08  #Partial instantiations: 0
% 1.50/1.08  #Strategies tried      : 1
% 1.50/1.08  
% 1.50/1.08  Timing (in seconds)
% 1.50/1.08  ----------------------
% 1.60/1.08  Preprocessing        : 0.26
% 1.60/1.08  Parsing              : 0.14
% 1.60/1.08  CNF conversion       : 0.01
% 1.60/1.08  Main loop            : 0.07
% 1.60/1.08  Inferencing          : 0.03
% 1.60/1.08  Reduction            : 0.02
% 1.60/1.08  Demodulation         : 0.02
% 1.60/1.08  BG Simplification    : 0.01
% 1.60/1.08  Subsumption          : 0.01
% 1.60/1.08  Abstraction          : 0.01
% 1.60/1.08  MUC search           : 0.00
% 1.60/1.08  Cooper               : 0.00
% 1.60/1.08  Total                : 0.35
% 1.60/1.08  Index Insertion      : 0.00
% 1.60/1.08  Index Deletion       : 0.00
% 1.60/1.08  Index Matching       : 0.00
% 1.60/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
