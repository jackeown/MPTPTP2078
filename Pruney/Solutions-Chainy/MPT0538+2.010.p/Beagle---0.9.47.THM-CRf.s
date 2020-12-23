%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:24 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_21,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_xboole_0(k2_relat_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_2'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( ~ v1_xboole_0(A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_75,plain,(
    ! [A_34,B_35] :
      ( k8_relat_1(A_34,B_35) = B_35
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_95,plain,(
    ! [B_37,B_38] :
      ( k8_relat_1(B_37,B_38) = B_38
      | ~ v1_relat_1(B_38)
      | ~ v1_xboole_0(k2_relat_1(B_38)) ) ),
    inference(resolution,[status(thm)],[c_42,c_75])).

tff(c_99,plain,(
    ! [B_39,A_40] :
      ( k8_relat_1(B_39,A_40) = A_40
      | ~ v1_relat_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_16,c_95])).

tff(c_103,plain,(
    ! [B_39] :
      ( k8_relat_1(B_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_107,plain,(
    ! [B_39] : k8_relat_1(B_39,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_103])).

tff(c_20,plain,(
    k8_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.17  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.62/1.17  
% 1.62/1.17  %Foreground sorts:
% 1.62/1.17  
% 1.62/1.17  
% 1.62/1.17  %Background operators:
% 1.62/1.17  
% 1.62/1.17  
% 1.62/1.17  %Foreground operators:
% 1.62/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.62/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.62/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.17  
% 1.86/1.18  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.86/1.18  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.86/1.18  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.86/1.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.86/1.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.86/1.18  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.86/1.18  tff(f_56, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.86/1.18  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.18  tff(c_21, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.18  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_21])).
% 1.86/1.18  tff(c_16, plain, (![A_11]: (v1_xboole_0(k2_relat_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.18  tff(c_38, plain, (![A_20, B_21]: (r2_hidden('#skF_2'(A_20, B_21), A_20) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.18  tff(c_42, plain, (![A_20, B_21]: (~v1_xboole_0(A_20) | r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.86/1.18  tff(c_75, plain, (![A_34, B_35]: (k8_relat_1(A_34, B_35)=B_35 | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.86/1.18  tff(c_95, plain, (![B_37, B_38]: (k8_relat_1(B_37, B_38)=B_38 | ~v1_relat_1(B_38) | ~v1_xboole_0(k2_relat_1(B_38)))), inference(resolution, [status(thm)], [c_42, c_75])).
% 1.86/1.18  tff(c_99, plain, (![B_39, A_40]: (k8_relat_1(B_39, A_40)=A_40 | ~v1_relat_1(A_40) | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_16, c_95])).
% 1.86/1.18  tff(c_103, plain, (![B_39]: (k8_relat_1(B_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_99])).
% 1.86/1.18  tff(c_107, plain, (![B_39]: (k8_relat_1(B_39, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25, c_103])).
% 1.86/1.18  tff(c_20, plain, (k8_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.18  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_20])).
% 1.86/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  Inference rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Ref     : 0
% 1.86/1.18  #Sup     : 21
% 1.86/1.18  #Fact    : 0
% 1.86/1.18  #Define  : 0
% 1.86/1.18  #Split   : 0
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 0
% 1.86/1.18  #Demod        : 2
% 1.86/1.18  #Tautology    : 6
% 1.86/1.18  #SimpNegUnit  : 0
% 1.86/1.18  #BackRed      : 1
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.18  Preprocessing        : 0.26
% 1.86/1.18  Parsing              : 0.15
% 1.86/1.18  CNF conversion       : 0.02
% 1.86/1.18  Main loop            : 0.14
% 1.86/1.18  Inferencing          : 0.07
% 1.86/1.18  Reduction            : 0.03
% 1.86/1.19  Demodulation         : 0.02
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.03
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.42
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
