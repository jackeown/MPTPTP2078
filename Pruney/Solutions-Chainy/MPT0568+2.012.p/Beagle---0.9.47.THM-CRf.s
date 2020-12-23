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
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_39,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_35,axiom,(
    ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [A_4] : k1_subset_1(A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_5] : v1_xboole_0(k1_subset_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_41,plain,(
    ! [A_12] :
      ( v1_relat_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_23,c_41])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [B_15,A_16] :
      ( r1_tarski(k10_relat_1(B_15,A_16),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_16] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_16),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_47])).

tff(c_52,plain,(
    ! [A_16] : r1_tarski(k10_relat_1(k1_xboole_0,A_16),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_50])).

tff(c_54,plain,(
    ! [A_18,B_19] :
      ( r2_xboole_0(A_18,B_19)
      | B_19 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_74,plain,(
    ! [A_16] : k10_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_70])).

tff(c_22,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.13  
% 1.56/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.13  %$ r2_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.56/1.13  
% 1.56/1.13  %Foreground sorts:
% 1.56/1.13  
% 1.56/1.13  
% 1.56/1.13  %Background operators:
% 1.56/1.13  
% 1.56/1.13  
% 1.56/1.13  %Foreground operators:
% 1.56/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.56/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.56/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.56/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.56/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.13  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.56/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.56/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.56/1.13  
% 1.56/1.14  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.56/1.14  tff(f_39, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.56/1.14  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.56/1.14  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.56/1.14  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.56/1.14  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.56/1.14  tff(f_35, axiom, (![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.56/1.14  tff(f_53, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.56/1.14  tff(c_10, plain, (![A_4]: (k1_subset_1(A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.56/1.14  tff(c_12, plain, (![A_5]: (v1_xboole_0(k1_subset_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.56/1.14  tff(c_23, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.56/1.14  tff(c_41, plain, (![A_12]: (v1_relat_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.56/1.14  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_23, c_41])).
% 1.56/1.14  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.56/1.14  tff(c_47, plain, (![B_15, A_16]: (r1_tarski(k10_relat_1(B_15, A_16), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.56/1.14  tff(c_50, plain, (![A_16]: (r1_tarski(k10_relat_1(k1_xboole_0, A_16), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_47])).
% 1.56/1.14  tff(c_52, plain, (![A_16]: (r1_tarski(k10_relat_1(k1_xboole_0, A_16), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_50])).
% 1.56/1.14  tff(c_54, plain, (![A_18, B_19]: (r2_xboole_0(A_18, B_19) | B_19=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.56/1.14  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.14  tff(c_70, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_8])).
% 1.56/1.14  tff(c_74, plain, (![A_16]: (k10_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_70])).
% 1.56/1.14  tff(c_22, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.56/1.14  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_22])).
% 1.56/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  Inference rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Ref     : 0
% 1.56/1.14  #Sup     : 12
% 1.56/1.14  #Fact    : 0
% 1.56/1.14  #Define  : 0
% 1.56/1.14  #Split   : 0
% 1.56/1.14  #Chain   : 0
% 1.56/1.14  #Close   : 0
% 1.56/1.14  
% 1.56/1.14  Ordering : KBO
% 1.56/1.14  
% 1.56/1.14  Simplification rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Subsume      : 0
% 1.56/1.14  #Demod        : 4
% 1.56/1.14  #Tautology    : 8
% 1.56/1.14  #SimpNegUnit  : 0
% 1.56/1.14  #BackRed      : 2
% 1.56/1.14  
% 1.56/1.14  #Partial instantiations: 0
% 1.56/1.14  #Strategies tried      : 1
% 1.56/1.14  
% 1.56/1.14  Timing (in seconds)
% 1.56/1.14  ----------------------
% 1.56/1.14  Preprocessing        : 0.24
% 1.56/1.14  Parsing              : 0.14
% 1.56/1.14  CNF conversion       : 0.01
% 1.56/1.14  Main loop            : 0.10
% 1.56/1.14  Inferencing          : 0.04
% 1.56/1.14  Reduction            : 0.03
% 1.56/1.14  Demodulation         : 0.02
% 1.56/1.14  BG Simplification    : 0.01
% 1.56/1.14  Subsumption          : 0.01
% 1.56/1.14  Abstraction          : 0.00
% 1.56/1.14  MUC search           : 0.00
% 1.56/1.14  Cooper               : 0.00
% 1.56/1.14  Total                : 0.37
% 1.56/1.14  Index Insertion      : 0.00
% 1.56/1.14  Index Deletion       : 0.00
% 1.56/1.14  Index Matching       : 0.00
% 1.56/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
