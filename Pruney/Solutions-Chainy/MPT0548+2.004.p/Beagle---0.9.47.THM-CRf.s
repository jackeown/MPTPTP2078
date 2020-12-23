%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:35 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  57 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_33,plain,(
    ! [A_15] :
      ( v1_relat_1(A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_33])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    ! [A_19,B_20] :
      ( r2_hidden('#skF_2'(A_19,B_20),A_19)
      | r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( ~ v1_xboole_0(A_19)
      | r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [B_33,A_34] :
      ( k7_relat_1(B_33,A_34) = B_33
      | ~ r1_tarski(k1_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_34] :
      ( k7_relat_1(k1_xboole_0,A_34) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_34)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_97,plain,(
    ! [A_35] :
      ( k7_relat_1(k1_xboole_0,A_35) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_92])).

tff(c_101,plain,(
    ! [B_20] :
      ( k7_relat_1(k1_xboole_0,B_20) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_111,plain,(
    ! [B_36] : k7_relat_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [B_36] :
      ( k9_relat_1(k1_xboole_0,B_36) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_16])).

tff(c_121,plain,(
    ! [B_36] : k9_relat_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_18,c_116])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:38:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.13  
% 1.73/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.14  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.73/1.14  
% 1.73/1.14  %Foreground sorts:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Background operators:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Foreground operators:
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.14  
% 1.73/1.15  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.73/1.15  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.73/1.15  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.73/1.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.73/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.73/1.15  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.73/1.15  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.73/1.15  tff(f_59, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.73/1.15  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.15  tff(c_33, plain, (![A_15]: (v1_relat_1(A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.73/1.15  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_33])).
% 1.73/1.15  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.15  tff(c_44, plain, (![A_19, B_20]: (r2_hidden('#skF_2'(A_19, B_20), A_19) | r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_48, plain, (![A_19, B_20]: (~v1_xboole_0(A_19) | r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.73/1.15  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.15  tff(c_81, plain, (![B_33, A_34]: (k7_relat_1(B_33, A_34)=B_33 | ~r1_tarski(k1_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.73/1.15  tff(c_92, plain, (![A_34]: (k7_relat_1(k1_xboole_0, A_34)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_34) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_81])).
% 1.73/1.15  tff(c_97, plain, (![A_35]: (k7_relat_1(k1_xboole_0, A_35)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_92])).
% 1.73/1.15  tff(c_101, plain, (![B_20]: (k7_relat_1(k1_xboole_0, B_20)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_97])).
% 1.73/1.15  tff(c_111, plain, (![B_36]: (k7_relat_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_101])).
% 1.73/1.15  tff(c_16, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.73/1.15  tff(c_116, plain, (![B_36]: (k9_relat_1(k1_xboole_0, B_36)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_111, c_16])).
% 1.73/1.15  tff(c_121, plain, (![B_36]: (k9_relat_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_18, c_116])).
% 1.73/1.15  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.73/1.15  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_24])).
% 1.73/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  Inference rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Ref     : 0
% 1.73/1.15  #Sup     : 24
% 1.73/1.15  #Fact    : 0
% 1.73/1.15  #Define  : 0
% 1.73/1.15  #Split   : 0
% 1.73/1.15  #Chain   : 0
% 1.73/1.15  #Close   : 0
% 1.73/1.15  
% 1.73/1.15  Ordering : KBO
% 1.73/1.15  
% 1.73/1.15  Simplification rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Subsume      : 0
% 1.73/1.15  #Demod        : 7
% 1.73/1.15  #Tautology    : 13
% 1.73/1.15  #SimpNegUnit  : 0
% 1.73/1.15  #BackRed      : 1
% 1.73/1.15  
% 1.73/1.15  #Partial instantiations: 0
% 1.73/1.15  #Strategies tried      : 1
% 1.73/1.15  
% 1.73/1.15  Timing (in seconds)
% 1.73/1.15  ----------------------
% 1.73/1.15  Preprocessing        : 0.26
% 1.73/1.15  Parsing              : 0.15
% 1.73/1.15  CNF conversion       : 0.02
% 1.73/1.15  Main loop            : 0.13
% 1.73/1.15  Inferencing          : 0.06
% 1.73/1.15  Reduction            : 0.03
% 1.73/1.15  Demodulation         : 0.02
% 1.73/1.15  BG Simplification    : 0.01
% 1.73/1.15  Subsumption          : 0.02
% 1.73/1.15  Abstraction          : 0.01
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.42
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
