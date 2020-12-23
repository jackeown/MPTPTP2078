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
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  51 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(k1_relat_1(B_36),A_37) = k1_relat_1(k7_relat_1(B_36,A_37))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_16,A_17] : r1_tarski(k3_xboole_0(B_16,A_17),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_133,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_36,A_37)),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_37])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,C_23)
      | ~ r1_xboole_0(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_22] :
      ( r1_xboole_0(A_22,'#skF_2')
      | ~ r1_tarski(A_22,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_111,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_160,plain,(
    ! [B_40] :
      ( k7_relat_1(B_40,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_40)
      | ~ r1_tarski(k1_relat_1(B_40),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_75,c_111])).

tff(c_293,plain,(
    ! [B_56] :
      ( k7_relat_1(k7_relat_1(B_56,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_56,'#skF_1'))
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_133,c_160])).

tff(c_299,plain,(
    ! [A_57] :
      ( k7_relat_1(k7_relat_1(A_57,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_8,c_293])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_317,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_16])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.24  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.11/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.24  
% 2.11/1.25  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.11/1.25  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.11/1.25  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.11/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.11/1.25  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.11/1.25  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.11/1.25  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.11/1.25  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.25  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.25  tff(c_121, plain, (![B_36, A_37]: (k3_xboole_0(k1_relat_1(B_36), A_37)=k1_relat_1(k7_relat_1(B_36, A_37)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.25  tff(c_22, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.25  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.25  tff(c_37, plain, (![B_16, A_17]: (r1_tarski(k3_xboole_0(B_16, A_17), A_17))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4])).
% 2.11/1.25  tff(c_133, plain, (![B_36, A_37]: (r1_tarski(k1_relat_1(k7_relat_1(B_36, A_37)), A_37) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_121, c_37])).
% 2.11/1.25  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.25  tff(c_72, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, C_23) | ~r1_xboole_0(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.25  tff(c_75, plain, (![A_22]: (r1_xboole_0(A_22, '#skF_2') | ~r1_tarski(A_22, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_72])).
% 2.11/1.25  tff(c_111, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.25  tff(c_160, plain, (![B_40]: (k7_relat_1(B_40, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_40) | ~r1_tarski(k1_relat_1(B_40), '#skF_1'))), inference(resolution, [status(thm)], [c_75, c_111])).
% 2.11/1.25  tff(c_293, plain, (![B_56]: (k7_relat_1(k7_relat_1(B_56, '#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_56, '#skF_1')) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_133, c_160])).
% 2.11/1.25  tff(c_299, plain, (![A_57]: (k7_relat_1(k7_relat_1(A_57, '#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_8, c_293])).
% 2.11/1.25  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.25  tff(c_317, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_299, c_16])).
% 2.11/1.25  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_317])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 79
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 0
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 14
% 2.11/1.25  #Demod        : 4
% 2.11/1.25  #Tautology    : 17
% 2.11/1.25  #SimpNegUnit  : 0
% 2.11/1.25  #BackRed      : 0
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.25  Preprocessing        : 0.28
% 2.11/1.25  Parsing              : 0.14
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.22
% 2.11/1.25  Inferencing          : 0.08
% 2.11/1.25  Reduction            : 0.06
% 2.11/1.25  Demodulation         : 0.05
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.05
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.53
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
