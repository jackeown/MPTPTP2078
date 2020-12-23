%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:06 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  34 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_4,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_7] :
      ( k7_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_8,plain,(
    ! [C_4,A_2,B_3] :
      ( k7_relat_1(k7_relat_1(C_4,A_2),B_3) = k7_relat_1(C_4,A_2)
      | ~ r1_tarski(A_2,B_3)
      | ~ v1_relat_1(C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_37,plain,(
    ! [B_3] :
      ( k7_relat_1(k1_xboole_0,B_3) = k7_relat_1('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_3)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8])).

tff(c_41,plain,(
    ! [B_3] : k7_relat_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_18,c_37])).

tff(c_12,plain,(
    k7_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.40  
% 1.96/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.40  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.96/1.40  
% 1.96/1.40  %Foreground sorts:
% 1.96/1.40  
% 1.96/1.40  
% 1.96/1.40  %Background operators:
% 1.96/1.40  
% 1.96/1.40  
% 1.96/1.40  %Foreground operators:
% 1.96/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.40  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.40  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.40  
% 1.96/1.41  tff(f_32, axiom, (?[A]: (~v1_xboole_0(A) & v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relat_1)).
% 1.96/1.41  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.96/1.41  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.96/1.41  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.96/1.41  tff(f_45, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.96/1.41  tff(c_4, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.41  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.41  tff(c_14, plain, (![A_7]: (k7_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.41  tff(c_18, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.96/1.41  tff(c_8, plain, (![C_4, A_2, B_3]: (k7_relat_1(k7_relat_1(C_4, A_2), B_3)=k7_relat_1(C_4, A_2) | ~r1_tarski(A_2, B_3) | ~v1_relat_1(C_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.41  tff(c_37, plain, (![B_3]: (k7_relat_1(k1_xboole_0, B_3)=k7_relat_1('#skF_1', k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_3) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8])).
% 1.96/1.41  tff(c_41, plain, (![B_3]: (k7_relat_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_18, c_37])).
% 1.96/1.41  tff(c_12, plain, (k7_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.41  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_12])).
% 1.96/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.41  
% 1.96/1.41  Inference rules
% 1.96/1.41  ----------------------
% 1.96/1.41  #Ref     : 0
% 1.96/1.41  #Sup     : 8
% 1.96/1.41  #Fact    : 0
% 1.96/1.41  #Define  : 0
% 1.96/1.41  #Split   : 0
% 1.96/1.41  #Chain   : 0
% 1.96/1.41  #Close   : 0
% 1.96/1.41  
% 1.96/1.41  Ordering : KBO
% 1.96/1.41  
% 1.96/1.41  Simplification rules
% 1.96/1.41  ----------------------
% 1.96/1.41  #Subsume      : 0
% 1.96/1.41  #Demod        : 4
% 1.96/1.41  #Tautology    : 4
% 1.96/1.41  #SimpNegUnit  : 0
% 1.96/1.41  #BackRed      : 1
% 1.96/1.41  
% 1.96/1.41  #Partial instantiations: 0
% 1.96/1.41  #Strategies tried      : 1
% 1.96/1.41  
% 1.96/1.41  Timing (in seconds)
% 1.96/1.42  ----------------------
% 1.96/1.42  Preprocessing        : 0.42
% 1.96/1.42  Parsing              : 0.23
% 1.96/1.42  CNF conversion       : 0.02
% 1.96/1.42  Main loop            : 0.15
% 1.96/1.42  Inferencing          : 0.08
% 1.96/1.42  Reduction            : 0.04
% 1.96/1.42  Demodulation         : 0.03
% 1.96/1.42  BG Simplification    : 0.01
% 1.96/1.42  Subsumption          : 0.01
% 1.96/1.42  Abstraction          : 0.01
% 1.96/1.42  MUC search           : 0.00
% 1.96/1.42  Cooper               : 0.00
% 1.96/1.42  Total                : 0.61
% 1.96/1.42  Index Insertion      : 0.00
% 1.96/1.42  Index Deletion       : 0.00
% 1.96/1.42  Index Matching       : 0.00
% 1.96/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
