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
% DateTime   : Thu Dec  3 09:59:59 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_27])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_2'(A_24,B_25),A_24)
      | r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_26,B_27] :
      ( ~ v1_xboole_0(A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_54,c_14])).

tff(c_96,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ v1_xboole_0(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_22,c_58])).

tff(c_98,plain,(
    ! [A_39] :
      ( k7_relat_1(k1_xboole_0,A_39) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_101,plain,(
    ! [A_39] : k7_relat_1(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_98])).

tff(c_24,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_24])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  
% 1.69/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.69/1.12  
% 1.69/1.12  %Foreground sorts:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Background operators:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Foreground operators:
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.69/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.12  
% 1.69/1.13  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.69/1.13  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.69/1.13  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.69/1.13  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.69/1.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.69/1.13  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.69/1.13  tff(f_56, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.69/1.13  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.13  tff(c_27, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.13  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_27])).
% 1.69/1.13  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.69/1.13  tff(c_49, plain, (![A_24, B_25]: (r2_hidden('#skF_2'(A_24, B_25), A_24) | r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.13  tff(c_54, plain, (![A_26, B_27]: (~v1_xboole_0(A_26) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_49, c_2])).
% 1.69/1.13  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.13  tff(c_58, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_54, c_14])).
% 1.69/1.13  tff(c_96, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~v1_xboole_0(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_22, c_58])).
% 1.69/1.13  tff(c_98, plain, (![A_39]: (k7_relat_1(k1_xboole_0, A_39)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_96])).
% 1.69/1.13  tff(c_101, plain, (![A_39]: (k7_relat_1(k1_xboole_0, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31, c_98])).
% 1.69/1.13  tff(c_24, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.13  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_24])).
% 1.69/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  Inference rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Ref     : 0
% 1.69/1.13  #Sup     : 15
% 1.69/1.13  #Fact    : 0
% 1.69/1.13  #Define  : 0
% 1.69/1.13  #Split   : 0
% 1.69/1.13  #Chain   : 0
% 1.69/1.13  #Close   : 0
% 1.69/1.13  
% 1.69/1.13  Ordering : KBO
% 1.69/1.13  
% 1.69/1.13  Simplification rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Subsume      : 0
% 1.69/1.13  #Demod        : 5
% 1.69/1.13  #Tautology    : 6
% 1.69/1.13  #SimpNegUnit  : 0
% 1.69/1.13  #BackRed      : 1
% 1.69/1.13  
% 1.69/1.13  #Partial instantiations: 0
% 1.69/1.13  #Strategies tried      : 1
% 1.69/1.13  
% 1.69/1.13  Timing (in seconds)
% 1.69/1.13  ----------------------
% 1.69/1.13  Preprocessing        : 0.26
% 1.69/1.13  Parsing              : 0.14
% 1.69/1.13  CNF conversion       : 0.02
% 1.69/1.13  Main loop            : 0.12
% 1.69/1.13  Inferencing          : 0.05
% 1.69/1.13  Reduction            : 0.03
% 1.69/1.13  Demodulation         : 0.02
% 1.69/1.13  BG Simplification    : 0.01
% 1.69/1.13  Subsumption          : 0.02
% 1.69/1.13  Abstraction          : 0.00
% 1.69/1.13  MUC search           : 0.00
% 1.69/1.13  Cooper               : 0.00
% 1.69/1.13  Total                : 0.40
% 1.69/1.13  Index Insertion      : 0.00
% 1.69/1.13  Index Deletion       : 0.00
% 1.69/1.13  Index Matching       : 0.00
% 1.69/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
