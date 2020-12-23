%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:24 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k8_relat_1(A_11,B_12),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    ! [A_28,B_29] :
      ( r2_xboole_0(A_28,B_29)
      | B_29 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_2'(A_24,B_25),B_25)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [B_25,A_24] :
      ( ~ v1_xboole_0(B_25)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_64,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(B_30)
      | B_30 = A_31
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(resolution,[status(thm)],[c_49,c_47])).

tff(c_69,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | k8_relat_1(A_33,B_32) = B_32
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_71,plain,(
    ! [A_33] :
      ( k8_relat_1(A_33,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_74,plain,(
    ! [A_33] : k8_relat_1(A_33,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_22,plain,(
    k8_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.20  
% 1.80/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.20  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.80/1.20  
% 1.80/1.20  %Foreground sorts:
% 1.80/1.20  
% 1.80/1.20  
% 1.80/1.20  %Background operators:
% 1.80/1.20  
% 1.80/1.20  
% 1.80/1.20  %Foreground operators:
% 1.80/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.80/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.80/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.20  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.80/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.80/1.20  
% 1.80/1.21  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.80/1.21  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.80/1.21  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.80/1.21  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.80/1.21  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.80/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.80/1.21  tff(f_60, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.80/1.21  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.21  tff(c_24, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.21  tff(c_28, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_24])).
% 1.80/1.21  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k8_relat_1(A_11, B_12), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.21  tff(c_49, plain, (![A_28, B_29]: (r2_xboole_0(A_28, B_29) | B_29=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.21  tff(c_38, plain, (![A_24, B_25]: (r2_hidden('#skF_2'(A_24, B_25), B_25) | ~r2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.80/1.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.21  tff(c_47, plain, (![B_25, A_24]: (~v1_xboole_0(B_25) | ~r2_xboole_0(A_24, B_25))), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.80/1.21  tff(c_64, plain, (![B_30, A_31]: (~v1_xboole_0(B_30) | B_30=A_31 | ~r1_tarski(A_31, B_30))), inference(resolution, [status(thm)], [c_49, c_47])).
% 1.80/1.21  tff(c_69, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | k8_relat_1(A_33, B_32)=B_32 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_20, c_64])).
% 1.80/1.21  tff(c_71, plain, (![A_33]: (k8_relat_1(A_33, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_69])).
% 1.80/1.21  tff(c_74, plain, (![A_33]: (k8_relat_1(A_33, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_71])).
% 1.80/1.21  tff(c_22, plain, (k8_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.21  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_22])).
% 1.80/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  Inference rules
% 1.80/1.21  ----------------------
% 1.80/1.21  #Ref     : 0
% 1.80/1.21  #Sup     : 9
% 1.80/1.21  #Fact    : 0
% 1.80/1.21  #Define  : 0
% 1.80/1.21  #Split   : 0
% 1.80/1.21  #Chain   : 0
% 1.80/1.21  #Close   : 0
% 1.80/1.21  
% 1.80/1.21  Ordering : KBO
% 1.80/1.21  
% 1.80/1.21  Simplification rules
% 1.80/1.21  ----------------------
% 1.80/1.21  #Subsume      : 1
% 1.80/1.21  #Demod        : 2
% 1.80/1.21  #Tautology    : 3
% 1.80/1.21  #SimpNegUnit  : 0
% 1.80/1.21  #BackRed      : 1
% 1.80/1.21  
% 1.80/1.21  #Partial instantiations: 0
% 1.80/1.21  #Strategies tried      : 1
% 1.80/1.21  
% 1.80/1.21  Timing (in seconds)
% 1.80/1.21  ----------------------
% 1.80/1.21  Preprocessing        : 0.28
% 1.80/1.21  Parsing              : 0.16
% 1.80/1.21  CNF conversion       : 0.02
% 1.80/1.21  Main loop            : 0.11
% 1.80/1.21  Inferencing          : 0.05
% 1.80/1.21  Reduction            : 0.03
% 1.80/1.21  Demodulation         : 0.02
% 1.80/1.21  BG Simplification    : 0.01
% 1.80/1.21  Subsumption          : 0.02
% 1.80/1.21  Abstraction          : 0.00
% 1.80/1.21  MUC search           : 0.00
% 1.80/1.21  Cooper               : 0.00
% 1.80/1.21  Total                : 0.41
% 1.80/1.21  Index Insertion      : 0.00
% 1.80/1.21  Index Deletion       : 0.00
% 1.80/1.21  Index Matching       : 0.00
% 1.80/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
