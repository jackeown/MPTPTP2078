%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:25 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    3
%              Number of atoms          :   23 (  33 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_15,plain,(
    ! [A_7] :
      ( k7_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_15])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_38,plain,(
    ! [C_12,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_12,A_13),B_14) = k7_relat_1(C_12,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19,c_28,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:07:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.09  
% 1.62/1.09  %Foreground sorts:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Background operators:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Foreground operators:
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.62/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.09  
% 1.62/1.09  tff(f_44, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.62/1.09  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.62/1.09  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.62/1.09  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.62/1.09  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.09  tff(c_15, plain, (![A_7]: (k7_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.09  tff(c_19, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_15])).
% 1.62/1.09  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.09  tff(c_24, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.09  tff(c_28, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_24])).
% 1.62/1.09  tff(c_38, plain, (![C_12, A_13, B_14]: (k7_relat_1(k7_relat_1(C_12, A_13), B_14)=k7_relat_1(C_12, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.09  tff(c_10, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.09  tff(c_47, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_10])).
% 1.62/1.09  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_19, c_28, c_47])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 13
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 3
% 1.62/1.09  #Tautology    : 6
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.10  Preprocessing        : 0.25
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.01
% 1.62/1.10  Main loop            : 0.09
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.02
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.00
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.35
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
