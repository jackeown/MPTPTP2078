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
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_14,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_15,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_19,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_15])).

tff(c_10,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_20])).

tff(c_29,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_24])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_31,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_6])).

tff(c_33,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.06  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.58/1.06  
% 1.58/1.06  %Foreground sorts:
% 1.58/1.06  
% 1.58/1.06  
% 1.58/1.06  %Background operators:
% 1.58/1.06  
% 1.58/1.06  
% 1.58/1.06  %Foreground operators:
% 1.58/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.58/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.58/1.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.58/1.06  
% 1.58/1.07  tff(f_43, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.58/1.07  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.58/1.07  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.58/1.07  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.58/1.07  tff(c_14, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.07  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.07  tff(c_15, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.07  tff(c_19, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_15])).
% 1.58/1.07  tff(c_10, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.07  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.07  tff(c_24, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_20])).
% 1.58/1.07  tff(c_29, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_19, c_24])).
% 1.58/1.07  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.58/1.07  tff(c_31, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_6])).
% 1.58/1.07  tff(c_33, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_31])).
% 1.58/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.07  
% 1.58/1.07  Inference rules
% 1.58/1.07  ----------------------
% 1.58/1.07  #Ref     : 0
% 1.58/1.07  #Sup     : 4
% 1.58/1.07  #Fact    : 0
% 1.58/1.07  #Define  : 0
% 1.58/1.07  #Split   : 0
% 1.58/1.07  #Chain   : 0
% 1.58/1.07  #Close   : 0
% 1.58/1.07  
% 1.58/1.07  Ordering : KBO
% 1.58/1.07  
% 1.58/1.07  Simplification rules
% 1.58/1.07  ----------------------
% 1.58/1.07  #Subsume      : 0
% 1.58/1.07  #Demod        : 3
% 1.58/1.07  #Tautology    : 2
% 1.58/1.07  #SimpNegUnit  : 1
% 1.58/1.07  #BackRed      : 2
% 1.58/1.07  
% 1.58/1.07  #Partial instantiations: 0
% 1.58/1.07  #Strategies tried      : 1
% 1.58/1.07  
% 1.58/1.07  Timing (in seconds)
% 1.58/1.07  ----------------------
% 1.58/1.07  Preprocessing        : 0.24
% 1.58/1.07  Parsing              : 0.14
% 1.58/1.07  CNF conversion       : 0.01
% 1.58/1.07  Main loop            : 0.08
% 1.58/1.07  Inferencing          : 0.03
% 1.58/1.07  Reduction            : 0.02
% 1.58/1.07  Demodulation         : 0.02
% 1.58/1.07  BG Simplification    : 0.01
% 1.58/1.07  Subsumption          : 0.01
% 1.58/1.07  Abstraction          : 0.00
% 1.58/1.07  MUC search           : 0.00
% 1.58/1.07  Cooper               : 0.00
% 1.58/1.08  Total                : 0.34
% 1.58/1.08  Index Insertion      : 0.00
% 1.58/1.08  Index Deletion       : 0.00
% 1.58/1.08  Index Matching       : 0.00
% 1.58/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
