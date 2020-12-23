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
% DateTime   : Thu Dec  3 09:59:48 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(k7_relat_1(B,A),A) = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [C_7,A_8,B_9] :
      ( k7_relat_1(k7_relat_1(C_7,A_8),B_9) = k7_relat_1(C_7,k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27,plain,
    ( k7_relat_1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:54:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.05  
% 1.51/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.06  %$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.51/1.06  
% 1.51/1.06  %Foreground sorts:
% 1.51/1.06  
% 1.51/1.06  
% 1.51/1.06  %Background operators:
% 1.51/1.06  
% 1.51/1.06  
% 1.51/1.06  %Foreground operators:
% 1.51/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.51/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.51/1.06  
% 1.51/1.06  tff(f_36, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(k7_relat_1(B, A), A) = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_relat_1)).
% 1.51/1.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.51/1.06  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.51/1.06  tff(c_8, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.51/1.06  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.06  tff(c_18, plain, (![C_7, A_8, B_9]: (k7_relat_1(k7_relat_1(C_7, A_8), B_9)=k7_relat_1(C_7, k3_xboole_0(A_8, B_9)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.51/1.06  tff(c_6, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.51/1.06  tff(c_27, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_6])).
% 1.51/1.06  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_27])).
% 1.51/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.06  
% 1.51/1.06  Inference rules
% 1.51/1.06  ----------------------
% 1.51/1.06  #Ref     : 0
% 1.51/1.06  #Sup     : 7
% 1.51/1.06  #Fact    : 0
% 1.51/1.06  #Define  : 0
% 1.51/1.06  #Split   : 0
% 1.51/1.06  #Chain   : 0
% 1.51/1.06  #Close   : 0
% 1.51/1.06  
% 1.51/1.06  Ordering : KBO
% 1.51/1.06  
% 1.51/1.06  Simplification rules
% 1.51/1.06  ----------------------
% 1.51/1.06  #Subsume      : 0
% 1.51/1.06  #Demod        : 2
% 1.51/1.06  #Tautology    : 3
% 1.51/1.06  #SimpNegUnit  : 0
% 1.51/1.06  #BackRed      : 0
% 1.51/1.06  
% 1.51/1.06  #Partial instantiations: 0
% 1.51/1.06  #Strategies tried      : 1
% 1.51/1.06  
% 1.51/1.06  Timing (in seconds)
% 1.51/1.06  ----------------------
% 1.51/1.06  Preprocessing        : 0.24
% 1.51/1.07  Parsing              : 0.13
% 1.51/1.07  CNF conversion       : 0.01
% 1.51/1.07  Main loop            : 0.06
% 1.51/1.07  Inferencing          : 0.03
% 1.51/1.07  Reduction            : 0.02
% 1.51/1.07  Demodulation         : 0.01
% 1.51/1.07  BG Simplification    : 0.01
% 1.51/1.07  Subsumption          : 0.01
% 1.51/1.07  Abstraction          : 0.00
% 1.51/1.07  MUC search           : 0.00
% 1.51/1.07  Cooper               : 0.00
% 1.51/1.07  Total                : 0.33
% 1.51/1.07  Index Insertion      : 0.00
% 1.51/1.07  Index Deletion       : 0.00
% 1.51/1.07  Index Matching       : 0.00
% 1.51/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
