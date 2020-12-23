%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [B_11,A_12] :
      ( k7_relat_1(B_11,A_12) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_12)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_12] :
      ( k7_relat_1(k1_xboole_0,A_12) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_46,plain,(
    ! [A_13] : k7_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4,c_43])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_51,plain,(
    ! [A_13] :
      ( k9_relat_1(k1_xboole_0,A_13) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_56,plain,(
    ! [A_13] : k9_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10,c_51])).

tff(c_16,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:46:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.64/1.08  
% 1.64/1.08  %Foreground sorts:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Background operators:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Foreground operators:
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.64/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.08  
% 1.64/1.09  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.64/1.09  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.64/1.09  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.64/1.09  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.64/1.09  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.64/1.09  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.64/1.09  tff(f_48, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.64/1.09  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.64/1.09  tff(c_26, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.64/1.09  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.64/1.09  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.09  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.64/1.09  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.09  tff(c_40, plain, (![B_11, A_12]: (k7_relat_1(B_11, A_12)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_12) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.09  tff(c_43, plain, (![A_12]: (k7_relat_1(k1_xboole_0, A_12)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_12) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_40])).
% 1.64/1.09  tff(c_46, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4, c_43])).
% 1.64/1.09  tff(c_8, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.64/1.09  tff(c_51, plain, (![A_13]: (k9_relat_1(k1_xboole_0, A_13)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 1.64/1.09  tff(c_56, plain, (![A_13]: (k9_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10, c_51])).
% 1.64/1.09  tff(c_16, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.09  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 1.64/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  Inference rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Ref     : 0
% 1.64/1.09  #Sup     : 11
% 1.64/1.09  #Fact    : 0
% 1.64/1.09  #Define  : 0
% 1.64/1.09  #Split   : 0
% 1.64/1.09  #Chain   : 0
% 1.64/1.09  #Close   : 0
% 1.64/1.09  
% 1.64/1.09  Ordering : KBO
% 1.64/1.09  
% 1.64/1.09  Simplification rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Subsume      : 0
% 1.64/1.09  #Demod        : 5
% 1.64/1.09  #Tautology    : 8
% 1.64/1.09  #SimpNegUnit  : 0
% 1.64/1.09  #BackRed      : 1
% 1.64/1.09  
% 1.64/1.09  #Partial instantiations: 0
% 1.64/1.09  #Strategies tried      : 1
% 1.64/1.09  
% 1.64/1.09  Timing (in seconds)
% 1.64/1.09  ----------------------
% 1.64/1.10  Preprocessing        : 0.25
% 1.64/1.10  Parsing              : 0.14
% 1.64/1.10  CNF conversion       : 0.01
% 1.64/1.10  Main loop            : 0.09
% 1.64/1.10  Inferencing          : 0.04
% 1.64/1.10  Reduction            : 0.02
% 1.64/1.10  Demodulation         : 0.02
% 1.64/1.10  BG Simplification    : 0.01
% 1.64/1.10  Subsumption          : 0.01
% 1.64/1.10  Abstraction          : 0.00
% 1.64/1.10  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.36
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
