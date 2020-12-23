%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  24 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_xboole_0 > k2_wellord1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_8,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( k2_wellord1(k2_wellord1(C_5,A_3),B_4) = k2_wellord1(C_5,k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [C_8,A_9,B_10] :
      ( k2_wellord1(k2_wellord1(C_8,A_9),B_10) = k2_wellord1(C_8,k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_51,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_60,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_51])).

tff(c_64,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.08  %$ v1_relat_1 > k3_xboole_0 > k2_wellord1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.52/1.08  
% 1.52/1.08  %Foreground sorts:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Background operators:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Foreground operators:
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.52/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.52/1.08  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.52/1.08  
% 1.52/1.08  tff(f_36, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 1.52/1.08  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 1.52/1.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.52/1.08  tff(c_8, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.08  tff(c_4, plain, (![C_5, A_3, B_4]: (k2_wellord1(k2_wellord1(C_5, A_3), B_4)=k2_wellord1(C_5, k3_xboole_0(A_3, B_4)) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.52/1.08  tff(c_42, plain, (![C_8, A_9, B_10]: (k2_wellord1(k2_wellord1(C_8, A_9), B_10)=k2_wellord1(C_8, k3_xboole_0(A_9, B_10)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.08  tff(c_6, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.08  tff(c_51, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_6])).
% 1.52/1.08  tff(c_60, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_51])).
% 1.52/1.08  tff(c_64, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_60])).
% 1.52/1.08  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_64])).
% 1.52/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.08  
% 1.52/1.08  Inference rules
% 1.52/1.08  ----------------------
% 1.52/1.08  #Ref     : 0
% 1.52/1.08  #Sup     : 14
% 1.52/1.08  #Fact    : 0
% 1.52/1.08  #Define  : 0
% 1.52/1.08  #Split   : 0
% 1.52/1.08  #Chain   : 0
% 1.52/1.08  #Close   : 0
% 1.52/1.08  
% 1.52/1.08  Ordering : KBO
% 1.52/1.08  
% 1.52/1.08  Simplification rules
% 1.52/1.08  ----------------------
% 1.52/1.08  #Subsume      : 0
% 1.52/1.08  #Demod        : 3
% 1.52/1.08  #Tautology    : 10
% 1.52/1.08  #SimpNegUnit  : 0
% 1.52/1.08  #BackRed      : 0
% 1.52/1.08  
% 1.52/1.08  #Partial instantiations: 0
% 1.52/1.08  #Strategies tried      : 1
% 1.52/1.08  
% 1.52/1.08  Timing (in seconds)
% 1.52/1.08  ----------------------
% 1.52/1.09  Preprocessing        : 0.24
% 1.60/1.09  Parsing              : 0.12
% 1.60/1.09  CNF conversion       : 0.01
% 1.60/1.09  Main loop            : 0.08
% 1.60/1.09  Inferencing          : 0.03
% 1.60/1.09  Reduction            : 0.02
% 1.60/1.09  Demodulation         : 0.02
% 1.60/1.09  BG Simplification    : 0.01
% 1.60/1.09  Subsumption          : 0.01
% 1.60/1.09  Abstraction          : 0.00
% 1.60/1.09  MUC search           : 0.00
% 1.60/1.09  Cooper               : 0.00
% 1.60/1.09  Total                : 0.34
% 1.60/1.09  Index Insertion      : 0.00
% 1.60/1.09  Index Deletion       : 0.00
% 1.60/1.09  Index Matching       : 0.00
% 1.60/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
