%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:36 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_159,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden(k4_tarski('#skF_3'(A_47,B_48,C_49),A_47),C_49)
      | ~ r2_hidden(A_47,k9_relat_1(C_49,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_39,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_xboole_0(A_21,B_22)
      | ~ r2_hidden(C_23,k3_xboole_0(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [A_8,C_23] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_23,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_49,plain,(
    ! [C_23] : ~ r2_hidden(C_23,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_175,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,k9_relat_1(k1_xboole_0,B_48))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_159,c_49])).

tff(c_187,plain,(
    ! [A_50,B_51] : ~ r2_hidden(A_50,k9_relat_1(k1_xboole_0,B_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_175])).

tff(c_210,plain,(
    ! [B_51] : k9_relat_1(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_187])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n024.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 17:34:20 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.08  
% 1.60/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.09  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.60/1.09  
% 1.60/1.09  %Foreground sorts:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Background operators:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Foreground operators:
% 1.60/1.09  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.60/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.60/1.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.09  
% 1.77/1.10  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.77/1.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.77/1.10  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.77/1.10  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.77/1.10  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.77/1.10  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.77/1.10  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.77/1.10  tff(f_70, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.77/1.10  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.77/1.10  tff(c_33, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.77/1.10  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_33])).
% 1.77/1.10  tff(c_159, plain, (![A_47, B_48, C_49]: (r2_hidden(k4_tarski('#skF_3'(A_47, B_48, C_49), A_47), C_49) | ~r2_hidden(A_47, k9_relat_1(C_49, B_48)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.77/1.10  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.10  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.77/1.10  tff(c_39, plain, (![A_21, B_22, C_23]: (~r1_xboole_0(A_21, B_22) | ~r2_hidden(C_23, k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.10  tff(c_46, plain, (![A_8, C_23]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_39])).
% 1.77/1.10  tff(c_49, plain, (![C_23]: (~r2_hidden(C_23, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 1.77/1.10  tff(c_175, plain, (![A_47, B_48]: (~r2_hidden(A_47, k9_relat_1(k1_xboole_0, B_48)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_159, c_49])).
% 1.77/1.10  tff(c_187, plain, (![A_50, B_51]: (~r2_hidden(A_50, k9_relat_1(k1_xboole_0, B_51)))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_175])).
% 1.77/1.10  tff(c_210, plain, (![B_51]: (k9_relat_1(k1_xboole_0, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_187])).
% 1.77/1.10  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.77/1.10  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_24])).
% 1.77/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.10  
% 1.77/1.10  Inference rules
% 1.77/1.10  ----------------------
% 1.77/1.10  #Ref     : 0
% 1.77/1.10  #Sup     : 37
% 1.77/1.10  #Fact    : 0
% 1.77/1.10  #Define  : 0
% 1.77/1.10  #Split   : 0
% 1.77/1.10  #Chain   : 0
% 1.77/1.10  #Close   : 0
% 1.77/1.10  
% 1.77/1.10  Ordering : KBO
% 1.77/1.10  
% 1.77/1.10  Simplification rules
% 1.77/1.10  ----------------------
% 1.77/1.10  #Subsume      : 8
% 1.77/1.10  #Demod        : 12
% 1.77/1.10  #Tautology    : 11
% 1.77/1.10  #SimpNegUnit  : 1
% 1.77/1.10  #BackRed      : 2
% 1.77/1.10  
% 1.77/1.10  #Partial instantiations: 0
% 1.77/1.10  #Strategies tried      : 1
% 1.77/1.10  
% 1.77/1.10  Timing (in seconds)
% 1.77/1.10  ----------------------
% 1.77/1.10  Preprocessing        : 0.27
% 1.77/1.10  Parsing              : 0.16
% 1.77/1.10  CNF conversion       : 0.02
% 1.77/1.10  Main loop            : 0.16
% 1.77/1.10  Inferencing          : 0.07
% 1.77/1.10  Reduction            : 0.04
% 1.77/1.10  Demodulation         : 0.03
% 1.77/1.10  BG Simplification    : 0.01
% 1.77/1.10  Subsumption          : 0.03
% 1.77/1.10  Abstraction          : 0.01
% 1.77/1.10  MUC search           : 0.00
% 1.77/1.10  Cooper               : 0.00
% 1.77/1.10  Total                : 0.46
% 1.77/1.10  Index Insertion      : 0.00
% 1.77/1.10  Index Deletion       : 0.00
% 1.77/1.10  Index Matching       : 0.00
% 1.77/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
